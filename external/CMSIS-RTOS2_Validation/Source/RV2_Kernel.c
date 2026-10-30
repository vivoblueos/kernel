/*
 * Copyright (C) 2022 ARM Limited or its affiliates. All rights reserved.
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

#include "cmsis_rv2.h"

/*-----------------------------------------------------------------------------
 *      Test implementation
 *----------------------------------------------------------------------------*/
void Th_osKernelSuspend_1 (void *arg) __NO_RETURN;
void Th_osKernelResume_1  (void *arg) __NO_RETURN;

void Irq_osKernelInitialize       (void);
void Irq_osKernelGetInfo          (void);
void Irq_osKernelGetState         (void);
void Irq_osKernelStart            (void);
void Irq_osKernelLock             (void);
void Irq_osKernelUnlock           (void);
void Irq_osKernelRestoreLock      (void);
void Irq_osKernelSuspend          (void);
void Irq_osKernelResume           (void);
void Irq_osKernelGetTickCount     (void);
void Irq_osKernelGetTickFreq      (void);
void Irq_osKernelGetSysTimerCount (void);
void Irq_osKernelGetSysTimerFreq  (void);

/*-----------------------------------------------------------------------------
 *      Test cases
 *----------------------------------------------------------------------------*/

/*=======0=========1=========2=========3=========4=========5=========6=========7=========8=========9=========0=========1====*/
/**
\defgroup kernel_funcs Kernel Functions
\brief Kernel Information and Control Test Cases
\details
The Kernel Information and Control function group in CMSIS-RTOS provides means for obtain information about the system, the
underlying kernel and the CMSIS-RTOS API. The test cases check the functions return values and calls from an ISR.

@{
*/

/*=======0=========1=========2=========3=========4=========5=========6=========7=========8=========9=========0=========1====*/
/**
\brief Test case: TC_osKernelInitialize_1
\details
  - Call osKernelInitialize when the kernel is already initialized
  - Call osKernelInitialize from ISR
*/
void TC_osKernelInitialize_1 (void) {
#if (TC_OSKERNELINITIALIZE_1_EN)
  /* Call osKernelInitialize when the kernel is already initialized */
  ASSERT_TRUE (osKernelInitialize() == osError);

  /* Call osKernelInitialize from ISR */
  TST_IRQHandler = Irq_osKernelInitialize;
  Isr_osStatus = osOK;
  SetPendingIRQ(IRQ_A);
  ASSERT_TRUE (Isr_osStatus == osErrorISR);
#endif
}

/*-----------------------------------------------------------------------------
 * TC_osKernelInitialize_1: ISR handler
 *----------------------------------------------------------------------------*/
#if (TC_OSKERNELINITIALIZE_1_EN)
void Irq_osKernelInitialize (void) {
  Isr_osStatus = osKernelInitialize();
}
#endif

/*=======0=========1=========2=========3=========4=========5=========6=========7=========8=========9=========0=========1====*/
/**
\brief Test case: TC_osKernelGetInfo_1
\details
  - Call osKernelGetInfo and check that returned structures are populated
  - Call osKernelGetInfo with argument version equal to NULL
  - Call osKernelGetInfo with argument id_buf equal to NULL
  - Call osKernelGetInfo with argument id_size equal to 0
  - Call osKernelGetInfo from ISR
*/
void TC_osKernelGetInfo_1 (void) {
#if (TC_OSKERNELGETINFO_1_EN)
  char id[100U];
  osVersion_t os_version;

  os_version.api    = 0U;
  os_version.kernel = 0U;
  id[0] = '\0';

  /* Call osKernelGetInfo and check that returned structures are populated */
  ASSERT_TRUE (osKernelGetInfo(&os_version, id, sizeof(id)) == osOK);
  ASSERT_TRUE (os_version.api    != 0U);
  ASSERT_TRUE (os_version.kernel != 0U);
  ASSERT_TRUE (id[0] != '\0');

  /* Call osKernelGetInfo with argument version equal to NULL */
  id[0] = '\0';
  ASSERT_TRUE (osKernelGetInfo(NULL, id, sizeof(id)) == osOK);
  ASSERT_TRUE (id[0] != '\0');

  /* Call osKernelGetInfo with argument id_buf equal to NULL */
  os_version.api    = 0U;
  os_version.kernel = 0U;
  ASSERT_TRUE (osKernelGetInfo(&os_version, NULL, sizeof(id)) == osOK);
  ASSERT_TRUE (os_version.api    != 0U);
  ASSERT_TRUE (os_version.kernel != 0U);

  /* Call osKernelGetInfo with argument id_size equal to 0 */
  os_version.api    = 0U;
  os_version.kernel = 0U;
  id[0] = '\0';
  ASSERT_TRUE (osKernelGetInfo(&os_version, id, 0U) == osOK);
  ASSERT_TRUE (os_version.api    != 0U);
  ASSERT_TRUE (os_version.kernel != 0U);
  ASSERT_TRUE (id[0] == '\0');

  /* Call osKernelGetInfo from ISR */
  TST_IRQHandler = Irq_osKernelGetInfo;
  Isr_osStatus = osError;
  SetPendingIRQ(IRQ_A);
  ASSERT_TRUE (Isr_osStatus == osOK);
#endif
}

/*-----------------------------------------------------------------------------
 * TC_osKernelGetInfo_1: ISR handler
 *----------------------------------------------------------------------------*/
#if (TC_OSKERNELGETINFO_1_EN)
void Irq_osKernelGetInfo (void) {
  char id[100U];
  osVersion_t os_version;

  os_version.api    = 0U;
  os_version.kernel = 0U;
  id[0] = '\0';

  Isr_osStatus = osKernelGetInfo (&os_version, id, sizeof(id));
}
#endif

/*=======0=========1=========2=========3=========4=========5=========6=========7=========8=========9=========0=========1====*/
/**
\brief Test case:  TC_osKernelGetState_1
\details
  - Call osKernelGetState when the kernel is running
  - Call osKernelGetState when the kernel is locked
  - Call osKernelGetState after the kernel is unlocked
  - Call osKernelGetState from ISR
*/
void TC_osKernelGetState_1 (void) {
#if (TC_OSKERNELGETSTATE_1_EN)
  /* Call osKernelGetState when the kernel is running */
  ASSERT_TRUE (osKernelGetState() == osKernelRunning);

  /* Call osKernelGetState when the kernel is locked */
  osKernelLock();
  ASSERT_TRUE (osKernelGetState() == osKernelLocked);

  /* Call osKernelGetState after the kernel is unlocked */
  osKernelUnlock();
  ASSERT_TRUE (osKernelGetState() == osKernelRunning);

  /* Call osKernelGetState from ISR */
  TST_IRQHandler = Irq_osKernelGetState;
  Isr_osKernelState = osKernelError;
  SetPendingIRQ(IRQ_A);
  ASSERT_TRUE (Isr_osKernelState == osKernelRunning);
#endif
}

/*-----------------------------------------------------------------------------
 * TC_osKernelGetState_1: ISR handler
 *----------------------------------------------------------------------------*/
#if (TC_OSKERNELGETSTATE_1_EN)
void Irq_osKernelGetState (void) {
  Isr_osKernelState = osKernelGetState();
}
#endif

/*=======0=========1=========2=========3=========4=========5=========6=========7=========8=========9=========0=========1====*/
/**
\brief Test case:  TC_osKernelGetState_2
\details
  - Call osKernelGetState when the kernel is suspended
  - Call osKernelGetState after resuming the kernel
*/
void TC_osKernelGetState_2 (void) {
#if (TC_OSKERNELGETSTATE_2_EN)
  /* Call osKernelGetState when the kernel is suspended */
  osKernelSuspend ();
  ASSERT_TRUE (osKernelGetState() == osKernelSuspended);

  /* Call osKernelGetState after resuming the kernel */
  osKernelResume (0);
  ASSERT_TRUE (osKernelGetState() == osKernelRunning);
#endif
}

/*=======0=========1=========2=========3=========4=========5=========6=========7=========8=========9=========0=========1====*/
/**
\brief Test case: TC_osKernelStart_1
\details
  - Call osKernelStart when the kernel is already running
  - Call osKernelStart from ISR
*/
void TC_osKernelStart_1 (void) {
#if (TC_OSKERNELSTART_1_EN)
  /* Check the kernel is running */
  ASSERT_TRUE (osKernelGetState() == osKernelRunning);

  /* Call osKernelStart when the kernel is already running */
  ASSERT_TRUE (osKernelStart() == osError);

  /* Call osKernelStart from ISR */
  TST_IRQHandler = Irq_osKernelStart;
  Isr_osStatus = osOK;
  SetPendingIRQ(IRQ_A);
  ASSERT_TRUE (Isr_osStatus == osErrorISR);
#endif
}

/*-----------------------------------------------------------------------------
 * TC_osKernelStart_1: ISR handler
 *----------------------------------------------------------------------------*/
#if (TC_OSKERNELSTART_1_EN)
void Irq_osKernelStart (void) {
  Isr_osStatus = osKernelStart();
}
#endif

/*=======0=========1=========2=========3=========4=========5=========6=========7=========8=========9=========0=========1====*/
/**
\brief Test case: TC_osKernelLock_1
\details
  - Call osKernelLock to try lock already locked kernel
  - Call osKernelLock from ISR
*/
void TC_osKernelLock_1 (void) {
#if (TC_OSKERNELLOCK_1_EN)

  /* Lock kernel */
  ASSERT_TRUE (osKernelGetState() == osKernelRunning);
  ASSERT_TRUE (osKernelLock() == 0U);
  ASSERT_TRUE (osKernelGetState() == osKernelLocked);

  /* Call osKernelLock to try lock already locked kernel */
  ASSERT_TRUE (osKernelLock() == 1U);
  ASSERT_TRUE (osKernelGetState() == osKernelLocked);

  /* Unlock kernel */
  osKernelUnlock();
  /* Second call to account for osKernelLock nesting */
  osKernelUnlock();

  /* Call osKernelLock from ISR */
  TST_IRQHandler = Irq_osKernelLock;
  Isr_s32 = 0;
  SetPendingIRQ(IRQ_A);
  ASSERT_TRUE (Isr_s32 == (int32_t)osErrorISR);
#endif
}

/*-----------------------------------------------------------------------------
 * TC_osKernelLock_1: ISR handler
 *----------------------------------------------------------------------------*/
#if (TC_OSKERNELLOCK_1_EN)
void Irq_osKernelLock (void) {
  Isr_s32 = osKernelLock();
}
#endif

/*=======0=========1=========2=========3=========4=========5=========6=========7=========8=========9=========0=========1====*/
/**
\brief Test case: TC_osKernelLock_2
\details
  - Call osKernelLock to try lock suspended kernel
*/
void TC_osKernelLock_2 (void) {
#if (TC_OSKERNELLOCK_2_EN)
  /* Call osKernelLock to try lock suspended kernel */
  osKernelSuspend ();
  ASSERT_TRUE (osKernelGetState() == osKernelSuspended);
  ASSERT_TRUE (osKernelLock() == osError);
  ASSERT_TRUE (osKernelGetState() == osKernelSuspended);
  osKernelResume (0);
#endif
}

/*=======0=========1=========2=========3=========4=========5=========6=========7=========8=========9=========0=========1====*/
/**
\brief Test case: TC_osKernelUnlock_1
\details
  - Call osKernelUnlock to try unlock running kernel
  - Call osKernelUnlock from ISR
*/
void TC_osKernelUnlock_1 (void) {
#if (TC_OSKERNELUNLOCK_1_EN)
  /* Lock kernel */
  osKernelLock();

  /* Unlock kernel */
  ASSERT_TRUE (osKernelGetState() == osKernelLocked);
  ASSERT_TRUE (osKernelUnlock() == 1U);
  ASSERT_TRUE (osKernelGetState() == osKernelRunning);

  /* Call osKernelUnlock to try unlock running kernel */
  ASSERT_TRUE (osKernelUnlock() == 0U);
  ASSERT_TRUE (osKernelGetState() == osKernelRunning);

  /* Call osKernelUnlock from ISR */
  TST_IRQHandler = Irq_osKernelUnlock;
  Isr_s32 = 0;
  SetPendingIRQ(IRQ_A);
  ASSERT_TRUE (Isr_s32 == (int32_t)osErrorISR);
#endif
}

/*-----------------------------------------------------------------------------
 * TC_osKernelUnlock_1: ISR handler
 *----------------------------------------------------------------------------*/
#if (TC_OSKERNELUNLOCK_1_EN)
void Irq_osKernelUnlock (void) {
  Isr_s32 = osKernelUnlock();
}
#endif

/*=======0=========1=========2=========3=========4=========5=========6=========7=========8=========9=========0=========1====*/
/**
\brief Test case: TC_osKernelUnlock_2
\details
  - Call osKernelUnlock to try unlock suspended kernel
*/
void TC_osKernelUnlock_2 (void) {
#if (TC_OSKERNELUNLOCK_2_EN)

  /* Call osKernelUnlock to try unlock suspended kernel */
  osKernelSuspend ();
  ASSERT_TRUE (osKernelGetState() == osKernelSuspended);
  ASSERT_TRUE (osKernelUnlock() == osError);
  ASSERT_TRUE (osKernelGetState() == osKernelSuspended);
  osKernelResume (0);
#endif
}

/*=======0=========1=========2=========3=========4=========5=========6=========7=========8=========9=========0=========1====*/
/**
\brief Test case: TC_osKernelRestoreLock_1
\details
  - Call osKernelRestoreLock to lock kernel
  - Call osKernelRestoreLock to unlock kernel
  - Call osKernelRestoreLock from ISR
*/
void TC_osKernelRestoreLock_1 (void) {
#if (TC_OSKERNELRESTORELOCK_1_EN)
  /* Call osKernelRestoreLock to lock kernel */
  ASSERT_TRUE (osKernelGetState() == osKernelRunning);
  ASSERT_TRUE (osKernelRestoreLock(1U) == 1U);
  ASSERT_TRUE (osKernelGetState() == osKernelLocked);

  /* Call osKernelRestoreLock to unlock kernel */
  ASSERT_TRUE (osKernelRestoreLock(0U) == 0U);
  ASSERT_TRUE (osKernelGetState() == osKernelRunning);

  /* Call osKernelRestoreLock from ISR */
  TST_IRQHandler = Irq_osKernelRestoreLock;
  Isr_s32 = 0;
  SetPendingIRQ(IRQ_A);
  ASSERT_TRUE (Isr_s32 == (int32_t)osErrorISR);
#endif
}

/*-----------------------------------------------------------------------------
 * TC_osKernelRestoreLock_1: ISR handler
 *----------------------------------------------------------------------------*/
#if (TC_OSKERNELRESTORELOCK_1_EN)
void Irq_osKernelRestoreLock (void) {
  Isr_s32 = osKernelRestoreLock(0U);
}
#endif

/*=======0=========1=========2=========3=========4=========5=========6=========7=========8=========9=========0=========1====*/
/**
\brief Test case: TC_osKernelSuspend_1
\details
  - Call osKernelSuspend to suspend the kernel when no other RTOS objects are active
  - Call osKernelSuspend when the kernel is already suspended
  - Call osKernelSuspend to suspend the kernel with other RTOS objects active
  - Call osKernelSuspend from ISR
*/
void TC_osKernelSuspend_1 (void) {
#if (TC_OSKERNELSUSPEND_1_EN)
  osThreadAttr_t attr = { NULL, osThreadDetached, NULL, 0U, NULL, 0U, osPriorityAboveNormal, 0U, 0U};
  osThreadId_t   id;
  uint32_t       arg;

  /* Call osKernelSuspend to suspend the kernel when no other RTOS objects are active */
  ASSERT_TRUE (osKernelSuspend() == osWaitForever);
  ASSERT_TRUE (osKernelGetState() == osKernelSuspended);

  /* Call osKernelSuspend when the kernel is already suspended */
  ASSERT_TRUE (osKernelSuspend() == 0U);
  ASSERT_TRUE (osKernelGetState() == osKernelSuspended);

  /* Resume the kernel */
  osKernelResume(0U);

  /* Synchronize tick */
  osDelay(1U);

  /* Create higher priority thread */
  arg = 0U;
  id = osThreadNew(Th_osKernelSuspend_1, &arg, &attr);

  /* Call osKernelSuspend to suspend the kernel with other RTOS objects active */
  ASSERT_TRUE (osKernelSuspend() == 50U);
  ASSERT_TRUE (osKernelGetState() == osKernelSuspended);

  /* Check execution counter */
  ASSERT_TRUE (arg == 1U);

  /* Resume kernel */
  osKernelResume(50U);

  /* Check execution counter */
  ASSERT_TRUE (arg > 1U);

  /* Terminate the thread */
  ASSERT_TRUE (osThreadTerminate (id) == osOK);

  /* Call osKernelSuspend from ISR */
  TST_IRQHandler = Irq_osKernelSuspend;
  Isr_u32 = osWaitForever;
  SetPendingIRQ(IRQ_A);
  ASSERT_TRUE (Isr_u32 == 0U);
#endif
}

/*-----------------------------------------------------------------------------
 * TC_osKernelSuspend_1: Helper thread
 *----------------------------------------------------------------------------*/
#if (TC_OSKERNELSUSPEND_1_EN)
void Th_osKernelSuspend_1 (void *arg) {
  uint32_t *cnt = (uint32_t *)arg;

  for (;;) {
    /* Increment execution counter */
    (*cnt)++;

    /* Delay the thread for 50 ticks */
    osDelay(50U);
  }
}
#endif

/*-----------------------------------------------------------------------------
 * TC_osKernelSuspend_1: ISR handler
 *----------------------------------------------------------------------------*/
#if (TC_OSKERNELSUSPEND_1_EN)
void Irq_osKernelSuspend (void) {
  Isr_u32 = osKernelSuspend();
}
#endif

/*=======0=========1=========2=========3=========4=========5=========6=========7=========8=========9=========0=========1====*/
/**
\brief Test case: TC_osKernelResume_1
\details
  - Call osKernelResume to resume suspended kernel
  - Call osKernelResume from ISR
*/
void TC_osKernelResume_1 (void) {
#if (TC_OSKERNELRESUME_1_EN)
  osThreadAttr_t attr = { NULL, osThreadDetached, NULL, 0U, NULL, 0U, osPriorityAboveNormal, 0U, 0U};
  osThreadId_t   id;
  uint32_t       arg;
  uint32_t       cnt;

  /* Synchronize tick */
  osDelay(1U);

  /* Create a higher priority child thread that sets a variable and calls osDelay with 50 ticks */
  arg = 0U;
  id = osThreadNew(Th_osKernelResume_1, &arg, &attr);
  ASSERT_TRUE (id != NULL);
  ASSERT_TRUE (arg == 1U);

  /* Suspend kernel and check its state */
  ASSERT_TRUE (osKernelSuspend () == 50U);
  ASSERT_TRUE (osKernelGetState() == osKernelSuspended);

  cnt = osKernelGetTickCount();

  /* Call osKernelResume to resume suspended kernel */
  osKernelResume(50U);

  cnt = osKernelGetTickCount() - cnt;
  ASSERT_TRUE (osKernelGetState() == osKernelRunning);

  /* Check the tick count's difference */
  ASSERT_TRUE (cnt == 50U);

  /* Check whether child thread has been dispatched */
  ASSERT_TRUE (arg == 2U);

  /* Terminate the thread */
  ASSERT_TRUE (osThreadTerminate (id) == osOK);

  /* Suspend the kernel */
  ASSERT_TRUE (osKernelSuspend () > 0U);
  ASSERT_TRUE (osKernelGetState() == osKernelSuspended);

  /* Call osKernelResume from ISR */
  TST_IRQHandler = Irq_osKernelResume;
  SetPendingIRQ(IRQ_A);
  ASSERT_TRUE (osKernelGetState() == osKernelSuspended);

  /* Resume suspended kernel */
  osKernelResume(0U);
#endif
}

/*-----------------------------------------------------------------------------
 * TC_osKernelResume_1: Helper thread
 *----------------------------------------------------------------------------*/
#if (TC_OSKERNELRESUME_1_EN)
void Th_osKernelResume_1 (void *arg) {
  uint32_t *cnt = (uint32_t *)arg;

  for (;;) {
    /* Increment execution counter */
    (*cnt)++;

    /* Delay the thread for 50 ticks */
    osDelay(50U);
  }
}
#endif

/*-----------------------------------------------------------------------------
 * TC_osKernelResume_1: ISR handler
 *----------------------------------------------------------------------------*/
#if (TC_OSKERNELRESUME_1_EN)
void Irq_osKernelResume (void) {
  osKernelResume(0U);
}
#endif

/*=======0=========1=========2=========3=========4=========5=========6=========7=========8=========9=========0=========1====*/
/**
\brief Test case: TC_osKernelGetTickCount_1
\details
  - Call osKernelGetTickCount and check that returned value is non-zero
  - Call osKernelGetTickCount twice with an osDelay of 100 ticks in between
  - Call osKernelGetTickCount from ISR
*/
void TC_osKernelGetTickCount_1 (void) {
#if (TC_OSKERNELGETTICKCOUNT_EN)
  uint32_t cnt;

  /* Synchronize tick */
  osDelay(1U);

  /* Call osKernelGetTickCount and check that returned value is non-zero */
  ASSERT_TRUE (osKernelGetTickCount() > 0U);

  /* Synchronize tick */
  osDelay(1U);

  /* Call osKernelGetTickCount twice with an osDelay of 100 ticks in between */
  cnt = osKernelGetTickCount();
  osDelay(100U);
  cnt = osKernelGetTickCount() - cnt;
  ASSERT_TRUE (cnt == 100U);

  /* Call osKernelGetTickCount from ISR */
  TST_IRQHandler = Irq_osKernelGetTickCount;
  Isr_u32 = 0U;
  SetPendingIRQ(IRQ_A);
  ASSERT_TRUE (Isr_u32 > 0);
#endif
}

/*-----------------------------------------------------------------------------
 * TC_osKernelGetTickCount_1: ISR handler
 *----------------------------------------------------------------------------*/
#if (TC_OSKERNELGETTICKCOUNT_EN)
void Irq_osKernelGetTickCount (void) {
  Isr_u32 = osKernelGetTickCount();
}
#endif

/*=======0=========1=========2=========3=========4=========5=========6=========7=========8=========9=========0=========1====*/
/**
\brief Test case: TC_osKernelGetTickFreq_1
\details
  - Call osKernelGetTickFreq and check that returned value is non-zero
  - Call osKernelGetTickFreq and check that returned value equals to predefine tick frequency
  - Call osKernelGetTickFreq from ISR
*/
void TC_osKernelGetTickFreq_1 (void) {
#if (TC_OSKERNELGETTICKFREQ_EN)
  /* Call osKernelGetTickFreq and check that returned value is non-zero */
  ASSERT_TRUE (osKernelGetTickFreq() > 0U);

  /* Call osKernelGetTickFreq and check that returned value equals to predefine tick frequency */
  ASSERT_TRUE (osKernelGetTickFreq() == RTOS2_TICK_FREQ);

  /* Call osKernelGetTickFreq from ISR */
  TST_IRQHandler = Irq_osKernelGetTickFreq;
  Isr_u32 = 0U;
  SetPendingIRQ(IRQ_A);
  ASSERT_TRUE (Isr_u32 > 0);
#endif
}

/*-----------------------------------------------------------------------------
 * TC_osKernelGetTickFreq_1: ISR handler
 *----------------------------------------------------------------------------*/
#if (TC_OSKERNELGETTICKFREQ_EN)
void Irq_osKernelGetTickFreq (void) {
  Isr_u32 = osKernelGetTickFreq();
}
#endif

/*=======0=========1=========2=========3=========4=========5=========6=========7=========8=========9=========0=========1====*/
/**
\brief Test case: TC_osKernelGetSysTimerCount_1
\details
  - Call osKernelGetSysTimerCount and check that returned value is non-zero
  - Call osKernelGetSysTimerCount twice with an osDelay of 100 ticks in between
  - Call osKernelGetSysTimerCount from ISR
*/
void TC_osKernelGetSysTimerCount_1 (void) {
#if (TC_OSKERNELGETSYSTIMERCOUNT_EN)
  uint32_t cnt;

  /* Synchronize tick */
  osDelay(1U);

  /* Call osKernelGetSysTimerCount and check that returned value is non-zero */
  ASSERT_TRUE (osKernelGetSysTimerCount() > 0);

  /* Call osKernelGetSysTimerCount twice with an osDelay of 100 ticks in between */
  cnt = osKernelGetSysTimerCount();
  osDelay(100U);
  cnt = osKernelGetSysTimerCount() - cnt;
  cnt /= (osKernelGetSysTimerFreq()/RTOS2_TICK_FREQ);
  ASSERT_TRUE (cnt >=  99U);
  ASSERT_TRUE (cnt <= 101U);

  /* Call osKernelGetSysTimerCount from ISR */
  TST_IRQHandler = Irq_osKernelGetSysTimerCount;
  Isr_u32 = 0U;
  SetPendingIRQ(IRQ_A);
  ASSERT_TRUE (Isr_u32 > 0);
#endif
}

/*-----------------------------------------------------------------------------
 * TC_osKernelGetSysTimerCount_1: ISR handler
 *----------------------------------------------------------------------------*/
#if (TC_OSKERNELGETSYSTIMERCOUNT_EN)
void Irq_osKernelGetSysTimerCount (void) {
  Isr_u32 = osKernelGetSysTimerCount();
}
#endif

/*=======0=========1=========2=========3=========4=========5=========6=========7=========8=========9=========0=========1====*/
/**
\brief Test case: TC_osKernelGetSysTimerFreq_1
\details
  - Call osKernelGetSysTimerFreq and check that returned value is non-zero
  - Call osKernelGetSysTimerFreq from ISR
*/
void TC_osKernelGetSysTimerFreq_1 (void) {
#if (TC_OSKERNELGETSYSTIMERFREQ_EN)
  /* Call osKernelGetSysTimerFreq and check that returned value is non-zero */
  ASSERT_TRUE (osKernelGetSysTimerFreq() > 0U);

  /* Call osKernelGetSysTimerFreq from ISR */
  TST_IRQHandler = Irq_osKernelGetSysTimerFreq;
  Isr_u32 = 0U;
  SetPendingIRQ(IRQ_A);
  ASSERT_TRUE (Isr_u32 > 0);
#endif
}

/*-----------------------------------------------------------------------------
 * TC_osKernelGetSysTimerFreq_1: ISR handler
 *----------------------------------------------------------------------------*/
#if (TC_OSKERNELGETSYSTIMERFREQ_EN)
void Irq_osKernelGetSysTimerFreq (void) {
  Isr_u32 = osKernelGetSysTimerFreq();
}
#endif

/**
@}
*/
// end of group genwait_funcs
