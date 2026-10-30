/*
 * Copyright (C) 2022-2023 ARM Limited or its affiliates. All rights reserved.
 *
 * SPDX-License-Identifier: Apache-2.0
 *
 * Licensed under the Apache License, Version 2.0 (the License); you may
 * not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 * www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an AS IS BASIS, WITHOUT
 * WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

#ifndef CMSIS_RV2_H__
#define CMSIS_RV2_H__

#include "cmsis_os2.h"
#include "cmsis_compiler.h"

#include "RV2_Config.h"
#include "RV2_Common.h"

#include "tf_main.h"

/* Interrupt handling */
#define IRQ_A          2
#define IRQ_B          3

extern void EnableIRQ     (int32_t irq_num);
extern void DisableIRQ    (int32_t irq_num);
extern void SetPendingIRQ (int32_t irq_num);

extern void (*TST_IRQHandler_A)(void);
extern void (*TST_IRQHandler_B)(void);

#define TST_IRQHandler TST_IRQHandler_A

/* Validation helper functions */
extern int  cmsis_rv2 (void);
extern void TS_Init   (void);
extern void TS_Uninit (void);

/* Test cases */
extern void TC_osKernelInitialize_1       (void);
extern void TC_osKernelGetInfo_1          (void);
extern void TC_osKernelGetState_1         (void);
extern void TC_osKernelGetState_2         (void);
extern void TC_osKernelStart_1            (void);
extern void TC_osKernelLock_1             (void);
extern void TC_osKernelLock_2             (void);
extern void TC_osKernelUnlock_1           (void);
extern void TC_osKernelUnlock_2           (void);
extern void TC_osKernelRestoreLock_1      (void);
extern void TC_osKernelSuspend_1          (void);
extern void TC_osKernelResume_1           (void);
extern void TC_osKernelGetSysTimerCount_1 (void);
extern void TC_osKernelGetSysTimerFreq_1  (void);
extern void TC_osKernelGetTickCount_1     (void);
extern void TC_osKernelGetTickFreq_1      (void);
extern void TC_KernelInterrupts           (void);

extern void TC_osThreadNew_1              (void);
extern void TC_osThreadNew_2              (void);
extern void TC_osThreadNew_3              (void);
extern void TC_osThreadNew_4              (void);
extern void TC_osThreadNew_5              (void);
extern void TC_osThreadNew_6              (void);
extern void TC_osThreadNew_7              (void);
extern void TC_osThreadGetName_1          (void);
extern void TC_osThreadGetId_1            (void);
extern void TC_osThreadGetState_1         (void);
extern void TC_osThreadGetState_2         (void);
extern void TC_osThreadGetState_3         (void);
extern void TC_osThreadSetPriority_1      (void);
extern void TC_osThreadSetPriority_2      (void);
extern void TC_osThreadGetPriority_1      (void);
extern void TC_osThreadYield_1            (void);
extern void TC_osThreadSuspend_1          (void);
extern void TC_osThreadResume_1           (void);
extern void TC_osThreadResume_2           (void);
extern void TC_osThreadDetach_1           (void);
extern void TC_osThreadDetach_2           (void);
extern void TC_osThreadJoin_1             (void);
extern void TC_osThreadJoin_2             (void);
extern void TC_osThreadJoin_3             (void);
extern void TC_osThreadExit_1             (void);
extern void TC_osThreadTerminate_1        (void);
extern void TC_osThreadGetStackSize_1     (void);
extern void TC_osThreadGetStackSpace_1    (void);
extern void TC_osThreadGetCount_1         (void);
extern void TC_osThreadEnumerate_1        (void);
extern void TC_ThreadAllocation           (void);
extern void TC_ThreadNew                  (void);
extern void TC_ThreadMultiInstance        (void);
extern void TC_ThreadTerminate            (void);
extern void TC_ThreadRestart              (void);
extern void TC_ThreadPriorityExec         (void);
extern void TC_ThreadYield                (void);
extern void TC_ThreadSuspendResume        (void);
extern void TC_ThreadReturn               (void);
extern void TC_ThreadExit                 (void);

extern void TC_ThreadFlagsMainThread      (void);
extern void TC_ThreadFlagsChildThread     (void);
extern void TC_ThreadFlagsChildToParent   (void);
extern void TC_ThreadFlagsChildToChild    (void);
extern void TC_ThreadFlagsWaitTimeout     (void);
extern void TC_ThreadFlagsCheckTimeout    (void);
extern void TC_ThreadFlagsParam           (void);
extern void TC_ThreadFlagsInterrupts      (void);

extern void TC_GenWaitBasic               (void);
extern void TC_GenWaitInterrupts          (void);

extern void TC_osTimerNew_1               (void);
extern void TC_osTimerNew_2               (void);
extern void TC_osTimerNew_3               (void);
extern void TC_osTimerGetName_1           (void);
extern void TC_osTimerStart_1             (void);
extern void TC_osTimerStart_2             (void);
extern void TC_osTimerStop_1              (void);
extern void TC_osTimerStop_2              (void);
extern void TC_osTimerIsRunning_1         (void);
extern void TC_osTimerDelete_1            (void);
extern void TC_TimerAllocation            (void);
extern void TC_TimerOneShot               (void);
extern void TC_TimerPeriodic              (void);

extern void TC_osEventFlagsNew_1          (void);
extern void TC_osEventFlagsNew_2          (void);
extern void TC_osEventFlagsNew_3          (void);
extern void TC_osEventFlagsSet_1          (void);
extern void TC_osEventFlagsClear_1        (void);
extern void TC_osEventFlagsGet_1          (void);
extern void TC_osEventFlagsWait_1         (void);
extern void TC_osEventFlagsDelete_1       (void);
extern void TC_osEventFlagsGetName_1      (void);
extern void TC_EventFlagsAllocation       (void);
extern void TC_EventFlagsInterThreads     (void);
extern void TC_EventFlagsCheckTimeout     (void);
extern void TC_EventFlagsWaitTimeout      (void);
extern void TC_EventFlagsDeleteWaiting    (void);


extern void TC_osMutexNew_1               (void);
extern void TC_osMutexNew_2               (void);
extern void TC_osMutexNew_3               (void);
extern void TC_osMutexNew_4               (void);
extern void TC_osMutexNew_5               (void);
extern void TC_osMutexNew_6               (void);
extern void TC_osMutexGetName_1           (void);
extern void TC_osMutexAcquire_1           (void);
extern void TC_osMutexAcquire_2           (void);
extern void TC_osMutexRelease_1           (void);
extern void TC_osMutexGetOwner_1          (void);
extern void TC_osMutexDelete_1            (void);
extern void TC_MutexAllocation            (void);
extern void TC_MutexCheckTimeout          (void);
extern void TC_MutexRobust                (void);
extern void TC_MutexPrioInherit           (void);
extern void TC_MutexNestedAcquire         (void);
extern void TC_MutexPriorityInversion     (void);
extern void TC_MutexOwnership             (void);

extern void TC_osSemaphoreNew_1           (void);
extern void TC_osSemaphoreNew_2           (void);
extern void TC_osSemaphoreNew_3           (void);
extern void TC_osSemaphoreGetName_1       (void);
extern void TC_osSemaphoreAcquire_1       (void);
extern void TC_osSemaphoreRelease_1       (void);
extern void TC_osSemaphoreGetCount_1      (void);
extern void TC_osSemaphoreDelete_1        (void);
extern void TC_SemaphoreAllocation        (void);
extern void TC_SemaphoreCreateAndDelete   (void);
extern void TC_SemaphoreObtainCounting    (void);
extern void TC_SemaphoreObtainBinary      (void);
extern void TC_SemaphoreWaitForBinary     (void);
extern void TC_SemaphoreWaitForCounting   (void);
extern void TC_SemaphoreZeroCount         (void);
extern void TC_SemaphoreWaitTimeout       (void);
extern void TC_SemaphoreCheckTimeout      (void);

extern void TC_osMemoryPoolNew_1          (void);
extern void TC_osMemoryPoolNew_2          (void);
extern void TC_osMemoryPoolNew_3          (void);
extern void TC_osMemoryPoolGetName_1      (void);
extern void TC_osMemoryPoolAlloc_1        (void);
extern void TC_osMemoryPoolFree_1         (void);
extern void TC_osMemoryPoolGetCapacity_1  (void);
extern void TC_osMemoryPoolGetBlockSize_1 (void);
extern void TC_osMemoryPoolGetCount_1     (void);
extern void TC_osMemoryPoolGetSpace_1     (void);
extern void TC_osMemoryPoolDelete_1       (void);
extern void TC_MemPoolAllocation          (void);
extern void TC_MemPoolAllocAndFree        (void);
extern void TC_MemPoolAllocAndFreeComb    (void);
extern void TC_MemPoolZeroInit            (void);

extern void TC_osMessageQueueNew_1        (void);
extern void TC_osMessageQueueNew_2        (void);
extern void TC_osMessageQueueNew_3        (void);
extern void TC_osMessageQueueGetName_1    (void);
extern void TC_osMessageQueuePut_1        (void);
extern void TC_osMessageQueuePut_2        (void);
extern void TC_osMessageQueueGet_1        (void);
extern void TC_osMessageQueueGet_2        (void);
extern void TC_osMessageQueueGetCapacity_1(void);
extern void TC_osMessageQueueGetMsgSize_1 (void);
extern void TC_osMessageQueueGetCount_1   (void);
extern void TC_osMessageQueueGetSpace_1   (void);
extern void TC_osMessageQueueReset_1      (void);
extern void TC_osMessageQueueDelete_1     (void);
extern void TC_MsgQAllocation             (void);
extern void TC_MsgQBasic                  (void);
extern void TC_MsgQWait                   (void);
extern void TC_MsgQCheckTimeout           (void);

#endif /* CMSIS_RV2_H__ */
