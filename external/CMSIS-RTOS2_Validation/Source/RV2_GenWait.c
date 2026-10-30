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
void Irq_GenWaitInterrupts (void);

/*-----------------------------------------------------------------------------
 *      Test cases
 *----------------------------------------------------------------------------*/

/*=======0=========1=========2=========3=========4=========5=========6=========7=========8=========9=========0=========1====*/
/**
\defgroup genwait_funcs Generic Wait Functions
\brief Generic Wait Functions Test Cases
\details
The Generic Wait function group in CMSIS-RTOS provides means for a time delay and allow to wait for unspecified events. The
test cases check the functions osDelay and osDelayUntil and call the generic wait functions from an ISR.

@{
*/

/*=======0=========1=========2=========3=========4=========5=========6=========7=========8=========9=========0=========1====*/
/**
\brief Test case: TC_GenWaitBasic
\details
- Call osDelay and wait until delay is executed
- Call osDelayUntil and wait until delay is executed
*/
void TC_GenWaitBasic (void) {
#if (TC_GENWAITBASIC_EN)
  uint32_t cnt[2];
  osStatus_t status;

  /* Synchronize to start of tick */
  osDelay(1);

  /* Measure osDelay duration (in ticks) */
  cnt[0] = osKernelGetTickCount();
  status = osDelay(10);
  cnt[1] = osKernelGetTickCount();

  ASSERT_TRUE (status == osOK);
  ASSERT_TRUE ((cnt[1]-cnt[0]) == 10U);

  /* Measure osDelayUntil duration (in ticks) */
  cnt[0] = osKernelGetTickCount();
  ASSERT_TRUE (osDelayUntil (cnt[0] + 20U) == osOK);
  cnt[1] = osKernelGetTickCount();
  ASSERT_TRUE ((cnt[0] + 20U) == cnt[1]);

  cnt[0] = osKernelGetTickCount();
  ASSERT_TRUE (osDelayUntil (cnt[0] + 1000U) == osOK);
  cnt[1] = osKernelGetTickCount();

 ASSERT_TRUE ((cnt[0] + 1000U) == cnt[1]);
#endif
}

/*=======0=========1=========2=========3=========4=========5=========6=========7=========8=========9=========0=========1====*/
/**
\brief Test case: TC_GenWaitInterrupts
\details
- Call generic wait functions from the ISR
*/
void TC_GenWaitInterrupts (void) {
#if (TC_GENWAITINTERRUPTS_EN)
  TST_IRQHandler = Irq_GenWaitInterrupts;

  Isr_s32 = 0; /* Test: osDelay */
  Isr_osStatus = osOK;
  SetPendingIRQ(IRQ_A);
  ASSERT_TRUE (Isr_osStatus == osErrorISR);

  Isr_s32 = 1; /* Test: osDelayUntil */
  Isr_osStatus = osOK;
  SetPendingIRQ(IRQ_A);
  ASSERT_TRUE (Isr_osStatus == osErrorISR);
}
#endif

/*-----------------------------------------------------------------------------
 * TC_GenWaitInterrupts: ISR handler
 *----------------------------------------------------------------------------*/
#if (TC_GENWAITINTERRUPTS_EN)
void Irq_GenWaitInterrupts (void) {
  switch (Isr_s32) {
    case 0: Isr_osStatus = osDelay (10); break;
    case 1: Isr_osStatus = osDelayUntil (10); break;
  }
#endif
}
/**
@}
*/
// end of group genwait_funcs
