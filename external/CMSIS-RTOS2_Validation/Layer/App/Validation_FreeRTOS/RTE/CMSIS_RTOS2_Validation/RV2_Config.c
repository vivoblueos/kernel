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

#include <stdlib.h>
#include "cmsis_rv2.h"
#include "RV2_Config_Device.h"

#if defined(__CORTEX_A)
#include "irq_ctrl.h"
#endif

/* Prototypes */
void TST_IRQ_HANDLER_A (void);
void TST_IRQ_HANDLER_B (void);
void (*TST_IRQHandler_A)(void);
void (*TST_IRQHandler_B)(void);

/*
  Primary interrupt handler
*/
void TST_IRQ_HANDLER_A (void) {

  if (TST_IRQHandler_A != NULL) {
    TST_IRQHandler_A();
  }
}

/*
  Secondary interrupt handler
*/
void TST_IRQ_HANDLER_B (void) {

  if (TST_IRQHandler_B != NULL) {
    TST_IRQHandler_B();
  }
}

/*
  Test suite initialization
*/
void TS_Init (void) {

#if defined(__CORTEX_M)
  /* Set primary and secondary interrupt priority */
  NVIC_SetPriority ((IRQn_Type)TST_IRQ_NUM_A, 5U);
  NVIC_SetPriority ((IRQn_Type)TST_IRQ_NUM_B, 4U);

  /* Enable interrupts */
  NVIC_EnableIRQ((IRQn_Type)TST_IRQ_NUM_A);
  NVIC_EnableIRQ((IRQn_Type)TST_IRQ_NUM_B);

#elif defined(__CORTEX_A)
  /* Disable interrupts and clear potential pending bits */
  IRQ_Disable ((IRQn_ID_t)TST_IRQ_NUM_A);
  IRQ_Disable ((IRQn_ID_t)TST_IRQ_NUM_B);

  IRQ_ClearPending ((IRQn_ID_t)TST_IRQ_NUM_A);
  IRQ_ClearPending ((IRQn_ID_t)TST_IRQ_NUM_B);

  /* Set edge-triggered IRQ */
  IRQ_SetMode ((IRQn_ID_t)TST_IRQ_NUM_A, IRQ_MODE_TRIG_EDGE);
  IRQ_SetMode ((IRQn_ID_t)TST_IRQ_NUM_B, IRQ_MODE_TRIG_EDGE);

  /* Register interrupt handlers */
  IRQ_SetHandler((IRQn_ID_t)TST_IRQ_NUM_A, TST_IRQ_HANDLER_A);
  IRQ_SetHandler((IRQn_ID_t)TST_IRQ_NUM_B, TST_IRQ_HANDLER_B);

  /* Enable interrupts */
  IRQ_Enable((IRQn_ID_t)TST_IRQ_NUM_A);
  IRQ_Enable((IRQn_ID_t)TST_IRQ_NUM_B);
#endif
}

/*
  Test suite de-initialization
*/
void TS_Uninit (void) {
  /* Close debug session here */
  exit(0);
}

/*
  Enable interrupt trigger in the IRQ controller.
*/
void EnableIRQ (int32_t irq_num) {

  if (irq_num == IRQ_A) {
    irq_num = TST_IRQ_NUM_A;
  } else {
    irq_num = TST_IRQ_NUM_B;
  }

#if defined(__CORTEX_M)
  NVIC_EnableIRQ((IRQn_Type)irq_num);
#elif defined(__CORTEX_A)
  IRQ_Enable((IRQn_ID_t)irq_num);
#endif
}

/*
  Disable interrupt trigger in the IRQ controller.
*/
void DisableIRQ (int32_t irq_num) {

  if (irq_num == IRQ_A) {
    irq_num = TST_IRQ_NUM_A;
  } else {
    irq_num = TST_IRQ_NUM_B;
  }

#if defined(__CORTEX_M)
  NVIC_DisableIRQ((IRQn_Type)irq_num);
#elif defined(__CORTEX_A)
  IRQ_Disable((IRQn_ID_t)irq_num);
#endif
}

/*
  Set pending interrupt in the IRQ controller.
*/
void SetPendingIRQ (int32_t irq_num) {

  if (irq_num == IRQ_A) {
    irq_num = TST_IRQ_NUM_A;
  } else {
    irq_num = TST_IRQ_NUM_B;
  }

#if defined(__CORTEX_M)
  NVIC_SetPendingIRQ((IRQn_Type)irq_num);

  __DSB();
  __ISB();
  __DMB();

  while (NVIC_GetPendingIRQ((IRQn_Type)irq_num) != 0);

#elif defined(__CORTEX_A)
  __disable_irq();
  IRQ_SetPending((IRQn_ID_t)irq_num);
  __enable_irq();

  __DSB();
  __ISB();
  __DMB();

  while (IRQ_GetPending((IRQn_ID_t)irq_num) != 0);
#endif
}
