/** @file

  Copyright (c) 2016 HP Development Company, L.P.
  Copyright (c) 2016 - 2024, Arm Limited. All rights reserved.
  Copyright (c) 2021, Linaro Limited
  Copyright (c) 2023, Ventana Micro System Inc. All rights reserved.

  SPDX-License-Identifier: BSD-2-Clause-Patent

**/

#include <Base.h>
#include <Pi/PiMmCis.h>

#include <Library/BaseMemoryLib.h>
#include <Library/DebugLib.h>
#include <Library/HobLib.h>
#ifdef MM_FUZZ_CALIBRATE
  #include <Library/StandaloneMmMmuLib.h>
#endif

#include <Protocol/DebugSupport.h> // for EFI_SYSTEM_CONTEXT

#include <Guid/ZeroGuid.h>
#include <Guid/MmramMemoryReserve.h>

#include <StandaloneMmCpu.h>

EFI_STATUS
EFIAPI
MmFoundationEntryRegister (
  IN CONST EFI_MM_CONFIGURATION_PROTOCOL  *This,
  IN EFI_MM_ENTRY_POINT                   MmEntryPoint
  );

//
// On ARM platforms every event is expected to have a GUID associated with
// it. It will be used by the MM Entry point to find the handler for the
// event. It will either be populated in a EFI_MM_COMMUNICATE_HEADER by the
// caller of the event (e.g. MM_COMMUNICATE SMC) or by the CPU driver
// (e.g. during an asynchronous event). In either case, this context is
// maintained in single global variable because StandaloneMm is UP-migratable
// (which means it cannot run concurrently)
//
EFI_MM_COMMUNICATE_HEADER  *mGuidedEventContext    = NULL;
UINT64                     mGuidedEventContextSize = 0;

EFI_MM_CONFIGURATION_PROTOCOL  mMmConfig = {
  0,
  MmFoundationEntryRegister
};

EDKII_PI_MM_CPU_DRIVER_EP_PROTOCOL  mPiMmCpuDriverEpProtocol = {
  PiMmStandaloneMmCpuDriverEntry
};

STATIC EFI_MM_ENTRY_POINT            mMmEntryPoint      = NULL;
STATIC CONST ARM_MM_HANDLER_CONTEXT  *mMmHandlerContext = NULL;

#ifdef MM_FUZZ_CALIBRATE
//
// Dynamic HeapGuard: we wrap the MM pool allocator so that, while an
// MM_COMMUNICATE call is being serviced, EVERY MmAllocatePool allocation is
// page-backed with a trailing no-access guard page. The buffer is placed flush
// against the guard, so a read/write even one byte past it faults and is caught
// by the SP crash oracle (spm_shim_exceptions.S). The guard page is made
// no-access at runtime via the SPM memory-attributes SMC - the stand's TF-A is
// patched to allow that outside SP_STATE_RESET. CommBuffer (allocated below via
// mMmst->MmAllocatePool) is just one such guarded allocation.
//
#define HG_MAX_RECS  64

typedef struct {
  VOID                  *User;   // pointer handed back to the caller
  EFI_PHYSICAL_ADDRESS  Base;    // page-aligned allocation base
  UINTN                 Pages;   // total pages incl. the guard page
} HG_REC;

STATIC EFI_ALLOCATE_POOL     mOrigAllocatePool = NULL;
STATIC EFI_FREE_POOL         mOrigFreePool     = NULL;
STATIC HG_REC                mHgRecs[HG_MAX_RECS];
STATIC UINTN                 mHgCount   = 0;
STATIC BOOLEAN               mHgActive  = FALSE;  // guard only during a call
STATIC BOOLEAN               mHgInAlloc = FALSE;  // reentrancy guard

STATIC
EFI_STATUS
EFIAPI
HgAllocatePool (
  IN  EFI_MEMORY_TYPE  PoolType,
  IN  UINTN            Size,
  OUT VOID             **Buffer
  )
{
  EFI_STATUS            Status;
  EFI_PHYSICAL_ADDRESS  Base;
  EFI_PHYSICAL_ADDRESS  Guard;
  UINTN                 DataPages;
  UINTN                 AlignedSize;

  if (!mHgActive || mHgInAlloc || (Buffer == NULL) || (Size == 0) ||
      (mHgCount >= HG_MAX_RECS))
  {
    return mOrigAllocatePool (PoolType, Size, Buffer);
  }

  mHgInAlloc = TRUE;
  DataPages  = EFI_SIZE_TO_PAGES (Size);
  Status     = mMmst->MmAllocatePages (AllocateAnyPages, PoolType, DataPages + 1, &Base);
  if (EFI_ERROR (Status)) {
    mHgInAlloc = FALSE;
    return mOrigAllocatePool (PoolType, Size, Buffer);  // fall back, no guard
  }

  Guard  = Base + (UINTN)DataPages * EFI_PAGE_SIZE;
  Status = ArmSetMemoryRegionNoAccess (Guard, EFI_PAGE_SIZE);
  if (EFI_ERROR (Status)) {
    mMmst->MmFreePages (Base, DataPages + 1);
    mHgInAlloc = FALSE;
    return mOrigAllocatePool (PoolType, Size, Buffer);  // runtime attr denied
  }

  // Place the buffer flush against the guard (8-byte aligned start) so that an
  // overflow of even one byte past an 8-aligned request hits the guard page.
  AlignedSize = ALIGN_VALUE (Size, 8);
  *Buffer     = (VOID *)(UINTN)(Guard - AlignedSize);

  mHgRecs[mHgCount].User  = *Buffer;
  mHgRecs[mHgCount].Base  = Base;
  mHgRecs[mHgCount].Pages = DataPages + 1;
  mHgCount++;

  mHgInAlloc = FALSE;
  return EFI_SUCCESS;
}

STATIC
EFI_STATUS
EFIAPI
HgFreePool (
  IN VOID  *Buffer
  )
{
  UINTN                 Index;
  EFI_PHYSICAL_ADDRESS  Base;
  UINTN                 Pages;

  for (Index = 0; Index < mHgCount; Index++) {
    if (mHgRecs[Index].User == Buffer) {
      Base  = mHgRecs[Index].Base;
      Pages = mHgRecs[Index].Pages;
      // Restore the guard page to RW before the pages go back to the pool.
      ArmSetMemoryRegionReadWritePerm (Base + (UINTN)(Pages - 1) * EFI_PAGE_SIZE, EFI_PAGE_SIZE);
      mMmst->MmFreePages (Base, Pages);
      mHgRecs[Index] = mHgRecs[mHgCount - 1];  // compact
      mHgCount--;
      return EFI_SUCCESS;
    }
  }

  return mOrigFreePool (Buffer);
}

/**
  Install the dynamic HeapGuard pool wrappers. Runs once at SP boot from the CPU
  driver entry; guarding itself only kicks in while mHgActive is set.
**/
VOID
SetupHeapGuard (
  VOID
  )
{
  mOrigAllocatePool     = mMmst->MmAllocatePool;
  mOrigFreePool         = mMmst->MmFreePool;
  mMmst->MmAllocatePool = HgAllocatePool;
  mMmst->MmFreePool     = HgFreePool;
  DEBUG ((DEBUG_INFO, "HeapGuard: dynamic pool guard installed\n"));
}
#endif

/**
  The PI Standalone MM entry point for the CPU driver.

  @param  [in] MmHandlerContext     Arm specific Mm handler context.
  @param  [in] CommBufferAddr       Address of the communication buffer.

  @retval   EFI_SUCCESS             Success.
  @retval   EFI_INVALID_PARAMETER   A parameter was invalid.
  @retval   EFI_ACCESS_DENIED       Access not permitted.
  @retval   EFI_OUT_OF_RESOURCES    Out of resources.
  @retval   EFI_UNSUPPORTED         Operation not supported.
**/
EFI_STATUS
PiMmStandaloneMmCpuDriverEntry (
  IN CONST ARM_MM_HANDLER_CONTEXT  *MmHandlerContext,
  IN UINTN                         CommBufferAddr
  )
{
  EFI_MM_ENTRY_CONTEXT       MmEntryPointContext;
  UINTN                      CommBufferSize;
  EFI_MM_COMMUNICATE_HEADER  *FixedCtx;
  EFI_STATUS                 AllocStatus;

  if (mGuidedEventContext == NULL) {
    ASSERT (0);
    return EFI_NOT_STARTED;
  }

  // Perform parameter validation.
  if ((MmHandlerContext == NULL) || (CommBufferAddr == (UINTN)NULL)) {
    return EFI_INVALID_PARAMETER;
  }

  if (mMmEntryPoint == NULL) {
    DEBUG ((DEBUG_ERROR, "Mm Entry point Not Found\n"));
    return EFI_UNSUPPORTED;
  }

  // Find out the size of the buffer passed
  if (CompareGuid (
        &((EFI_MM_COMMUNICATE_HEADER *)CommBufferAddr)->HeaderGuid,
        &gEfiMmCommunicateHeaderV3Guid
        ))
  {
    // This is a v3 header. Size the per-call buffer by the ACTUAL message
    // (vendor-style), not by the whole BufferSize capacity: header + MessageSize.
    CommBufferSize = OFFSET_OF (EFI_MM_COMMUNICATE_HEADER_V3, MessageData) +
                     ((EFI_MM_COMMUNICATE_HEADER_V3 *)CommBufferAddr)->MessageSize;
  } else {
    // This is a v1 header
    // Find out the size of the buffer passed
    CommBufferSize = ((EFI_MM_COMMUNICATE_HEADER *)CommBufferAddr)->MessageLength +
                     OFFSET_OF (EFI_MM_COMMUNICATE_HEADER, Data);
  }

  // PER-CALL allocation of the secure buffer instead of the persistent fixed
  // buffer. CommBufferSize already = MessageLength + sizeof (EFI_MM_COMMUNICATE_HEADER),
  // i.e. the full header + payload. Save the fixed buffer in FixedCtx to restore
  // afterwards (keeps the NULL-check and the next call valid); the root MMI
  // handler reads mGuidedEventContext.
  FixedCtx = mGuidedEventContext;
 #ifdef MM_FUZZ_CALIBRATE
  // Turn on HeapGuard for the whole call: CommBuffer and every allocation the
  // handler makes via MmAllocatePool get a trailing no-access guard page.
  mHgActive = TRUE;
 #endif
  AllocStatus = mMmst->MmAllocatePool (
                         EfiRuntimeServicesData,
                         CommBufferSize,
                         (VOID **)&mGuidedEventContext
                         );
  if (EFI_ERROR (AllocStatus)) {
    mGuidedEventContext = FixedCtx;
   #ifdef MM_FUZZ_CALIBRATE
    mHgActive = FALSE;
   #endif
    return EFI_OUT_OF_RESOURCES;
  }

  DEBUG ((
    DEBUG_INFO,
    "MMCPU: per-call alloc req=%lu bytes @ %p\n",
    (UINT64)CommBufferSize,
    (VOID *)mGuidedEventContext
    ));

  CopyMem (mGuidedEventContext, (CONST VOID *)CommBufferAddr, CommBufferSize);
  mMmHandlerContext = MmHandlerContext;

  ZeroMem (&MmEntryPointContext, sizeof (EFI_MM_ENTRY_CONTEXT));

  // StandaloneMm UP-migratable which means it cannot run concurrently.
  // Therefore, set number of cpus as 1 and cpu number as 0.
  MmEntryPointContext.CurrentlyExecutingCpu = 0;
  MmEntryPointContext.NumberOfCpus          = 1;

  // Populate the MM system table with MP and state information
  mMmst->CurrentlyExecutingCpu = 0;
  mMmst->NumberOfCpus          = 1;
  mMmst->CpuSaveStateSize      = 0;
  mMmst->CpuSaveState          = NULL;

  mMmEntryPoint (&MmEntryPointContext);

  // Copy results back, free the per-call buffer, restore the fixed context.
  CopyMem ((VOID *)CommBufferAddr, (CONST VOID *)mGuidedEventContext, CommBufferSize);
  mMmst->MmFreePool (mGuidedEventContext);
  mGuidedEventContext = FixedCtx;
 #ifdef MM_FUZZ_CALIBRATE
  mHgActive = FALSE;
 #endif

  mMmHandlerContext = NULL;

  return EFI_SUCCESS;
}

/**
  Registers the MM foundation entry point.

  @param  [in] This               Pointer to the MM Configuration protocol.
  @param  [in] MmEntryPoint       Function pointer to the MM Entry point.

  @retval   EFI_SUCCESS             Success.
**/
EFI_STATUS
EFIAPI
MmFoundationEntryRegister (
  IN CONST EFI_MM_CONFIGURATION_PROTOCOL  *This,
  IN EFI_MM_ENTRY_POINT                   MmEntryPoint
  )
{
  // store the entry point in a global
  mMmEntryPoint = MmEntryPoint;
  return EFI_SUCCESS;
}

/**
  This function is the main entry point for an MM handler dispatch
  or communicate-based callback.

  @param  DispatchHandle  The unique handle assigned to this handler by
                          MmiHandlerRegister().
  @param  Context         Points to an optional handler context which was
                          specified when the handler was registered.
  @param  CommBuffer      A pointer to a collection of data in memory that will
                          be conveyed from a non-MM environment into an
                          MM environment.
  @param  CommBufferSize  The size of the CommBuffer.

  @return Status Code

**/
EFI_STATUS
EFIAPI
PiMmCpuTpFwRootMmiHandler (
  IN     EFI_HANDLE  DispatchHandle,
  IN     CONST VOID  *Context         OPTIONAL,
  IN OUT VOID        *CommBuffer      OPTIONAL,
  IN OUT UINTN       *CommBufferSize  OPTIONAL
  )
{
  EFI_STATUS                    Status;
  EFI_MM_COMMUNICATE_HEADER_V3  *GuidedEventContextV3;

  ASSERT (Context == NULL);
  ASSERT (CommBuffer == NULL);
  ASSERT (CommBufferSize == NULL);

  if (mGuidedEventContext == NULL) {
    return EFI_NOT_FOUND;
  }

  if (CompareGuid (
        &mGuidedEventContext->HeaderGuid,
        &gEfiMmCommunicateHeaderV3Guid
        ))
  {
    GuidedEventContextV3 = (EFI_MM_COMMUNICATE_HEADER_V3 *)mGuidedEventContext;
    DEBUG ((
      DEBUG_INFO,
      "CommBuffer - 0x%x, CommBufferSize - 0x%llx, MessageSize - 0x%llx\n",
      GuidedEventContextV3,
      GuidedEventContextV3->BufferSize,
      GuidedEventContextV3->MessageSize
      ));

    Status = mMmst->MmiManage (
                      &GuidedEventContextV3->MessageGuid,
                      mMmHandlerContext,
                      GuidedEventContextV3->MessageData,
                      (UINTN *)(&GuidedEventContextV3->MessageSize)
                      );
  } else {
    DEBUG ((
      DEBUG_INFO,
      "CommBuffer - 0x%x, CommBufferSize - 0x%x\n",
      mGuidedEventContext,
      mGuidedEventContext->MessageLength
      ));
    Status = mMmst->MmiManage (
                      &mGuidedEventContext->HeaderGuid,
                      mMmHandlerContext,
                      mGuidedEventContext->Data,
                      (UINTN *)(&mGuidedEventContext->MessageLength)
                      );
  }

  if (Status != EFI_SUCCESS) {
    DEBUG ((DEBUG_WARN, "Unable to manage Guided Event - %d\n", Status));
  }

  return Status;
}
