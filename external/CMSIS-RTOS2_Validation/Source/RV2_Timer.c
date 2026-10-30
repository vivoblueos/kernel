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

#include <string.h>
#include "cmsis_rv2.h"

/*-----------------------------------------------------------------------------
 *      Test implementation
 *----------------------------------------------------------------------------*/
#define MAX_TIMER_NUM  64

/* Timer callback prototypes */
void TimCb_Oneshot        (void *arg);
void TimCb_Periodic       (void *arg);
void TimCb_Running        (void *arg);
void TimCb_Dummy          (void *arg);
void TimCb_osTimerStart_2 (void *arg);

static volatile osStatus_t Cb_osStatus;

static volatile uint32_t Tim_Var;
static volatile uint32_t Tim_Var_Os;
static volatile uint32_t Tim_Var_Per;

void Irq_osTimerNew_1       (void);
void Irq_osTimerGetName_1   (void);
void Irq_osTimerStart_1     (void);
void Irq_osTimerStop_1      (void);
void Irq_osTimerIsRunning_1 (void);
void Irq_osTimerDelete_1    (void);

/*-----------------------------------------------------------------------------
 *      One shoot timer
 *----------------------------------------------------------------------------*/
void TimCb_Oneshot  (void *arg) {
  uint32_t var = *(uint32_t *)arg;
  
  ASSERT_TRUE (var != 0);
  Tim_Var_Os += 1U;
}


/*-----------------------------------------------------------------------------
 *      Periodic timer
 *----------------------------------------------------------------------------*/
void TimCb_Periodic (void *arg) {
  uint32_t var = *(uint32_t *)arg;
  
  ASSERT_TRUE (var != 0);
  Tim_Var_Per += 1U;
}


/*-----------------------------------------------------------------------------
 *      Running (periodic) timer
 *----------------------------------------------------------------------------*/
void TimCb_Running (void __attribute__((unused)) *arg) {
  Tim_Var += 1;
}

/*-----------------------------------------------------------------------------
 *      Dummy timer callback
 *----------------------------------------------------------------------------*/
void TimCb_Dummy (void __attribute__((unused)) *arg) {
}

/*-----------------------------------------------------------------------------
 *      Test cases
 *----------------------------------------------------------------------------*/

/*=======0=========1=========2=========3=========4=========5=========6=========7=========8=========9=========0=========1====*/
/**
\defgroup timer_func Timer Functions
\brief Timer Functions Test Cases
\details
The test cases check the osTimer* functions.

@{
*/

/*=======0=========1=========2=========3=========4=========5=========6=========7=========8=========9=========0=========1====*/
/**
\brief Test case: TC_osTimerNew_1
\details
  - Call osTimerNew to create a timer object of type osTimerOnce
  - Call osTimerNew to create a timer object of type osTimerPeriodic
  - Call osTimerNew from ISR
  - Call osTimerNew with null timer function
*/
void TC_osTimerNew_1 (void) {
#if (TC_OSTIMERNEW_1_EN)
  osTimerId_t id;

  /* Call osTimerNew to create a timer object of type osTimerOnce */
  id = osTimerNew (TimCb_Dummy, osTimerOnce, NULL, NULL);
  ASSERT_TRUE (id != NULL);

  /* Delete created timer */
  ASSERT_TRUE (osTimerDelete(id) == osOK);

  /* Call osTimerNew to create a timer object of type osTimerPeriodic */
  id = osTimerNew (TimCb_Dummy, osTimerPeriodic, NULL, NULL);
  ASSERT_TRUE (id != NULL);

  /* Delete created timer */
  ASSERT_TRUE (osTimerDelete(id) == osOK);

  /* Call osTimerNew from ISR */
  TST_IRQHandler = Irq_osTimerNew_1;
  TimerId = (osTimerId_t)(-1);
  SetPendingIRQ(IRQ_A);
  ASSERT_TRUE (TimerId == NULL);

  /* Call osTimerNew with null timer function */
  ASSERT_TRUE (osTimerNew (NULL, osTimerOnce, NULL, NULL) == NULL);
#endif
}

/*-----------------------------------------------------------------------------
 * TC_osTimerNew_1: ISR handler
 *----------------------------------------------------------------------------*/
#if (TC_OSTIMERNEW_1_EN)
void Irq_osTimerNew_1 (void) {
  TimerId = osTimerNew (TimCb_Dummy, osTimerPeriodic, NULL, NULL);
}
#endif

/*=======0=========1=========2=========3=========4=========5=========6=========7=========8=========9=========0=========1====*/
/**
\brief Test case: TC_osTimerNew_2
\details
  - Call osTimerNew to create timer object and assign a name to it
*/
void TC_osTimerNew_2 (void) {
#if (TC_OSTIMERNEW_2_EN)
  osTimerAttr_t attr = {NULL, 0U, NULL, 0U};
  osTimerId_t id;

  /* Call osTimerNew to create timer object and assign a name to it */
  attr.name = "Timer";

  id = osTimerNew (TimCb_Dummy, osTimerOnce, NULL, &attr);
  ASSERT_TRUE (id != NULL);

  /* Delete created timer */
  ASSERT_TRUE (osTimerDelete(id) == osOK);
#endif
}

/*=======0=========1=========2=========3=========4=========5=========6=========7=========8=========9=========0=========1====*/
/**
\brief Test case: TC_osTimerNew_3
\details
  - Call osTimerNew to create timer object by specifying memory for control block in attributes
*/
void TC_osTimerNew_3 (void) {
#if (TC_OSTIMERNEW_3_EN)
  osTimerAttr_t attr = {NULL, 0U, NULL, 0U};
  osTimerId_t id;

  /* Call osTimerNew to create timer object by specifying memory for control block in attributes */
  attr.cb_mem  = &Timer_CbMem;
  attr.cb_size = sizeof(Timer_CbMem);

  id = osTimerNew (TimCb_Dummy, osTimerPeriodic, NULL, &attr);
  ASSERT_TRUE (id != NULL);

  /* Delete created timer */
  ASSERT_TRUE (osTimerDelete(id) == osOK);
#endif
}

/*=======0=========1=========2=========3=========4=========5=========6=========7=========8=========9=========0=========1====*/
/**
\brief Test case: TC_osTimerGetName_1
\details
  - Call osTimerGetName to retrieve a name of an unnamed timer
  - Call osTimerGetName to retrieve a name of a timer with assigned name
  - Call osTimerGetName from ISR
  - Call osTimerGetName with null object
*/
void TC_osTimerGetName_1 (void) {
#if (TC_OSTIMERGETNAME_1_EN)
  osTimerAttr_t attr = {NULL, 0U, NULL, 0U};
  osTimerId_t tid;
  char const *name = "Timer";

  /* Create timer object without assigned name */
  attr.name = NULL;
  tid = osTimerNew (TimCb_Dummy, osTimerOnce, NULL, &attr);
  ASSERT_TRUE (tid != NULL);

  /* Call osTimerGetName to retrieve a name of an unnamed timer */
  ASSERT_TRUE(osTimerGetName (tid) == NULL);

  /* Delete timer object */
  osTimerDelete (tid);


  /* Create timer object with name assigned via attributes */
  attr.name = name;
  tid = osTimerNew (TimCb_Dummy, osTimerOnce, NULL, &attr);
  ASSERT_TRUE (tid != NULL);

  /* Call osTimerGetName to retrieve a name of a timer with assigned name */
  ASSERT_TRUE (strcmp(osTimerGetName(tid), name) == 0U);

  /* Call osTimerGetName from ISR */
  TST_IRQHandler = Irq_osTimerGetName_1;
  TimerId   = tid;
  TimerName = name;
  SetPendingIRQ(IRQ_A);
  ASSERT_TRUE (strcmp(TimerName, name) == 0U);

  /* Delete timer object */
  osTimerDelete (tid);

  /* Call osTimerGetName with null object */
  ASSERT_TRUE (osTimerGetName (NULL) == NULL);
#endif
}

/*-----------------------------------------------------------------------------
 * TC_osTimerGetName_1: ISR handler
 *----------------------------------------------------------------------------*/
#if (TC_OSTIMERGETNAME_1_EN)
void Irq_osTimerGetName_1 (void) {
  TimerName = osTimerGetName (TimerId);
}
#endif

/*=======0=========1=========2=========3=========4=========5=========6=========7=========8=========9=========0=========1====*/
/**
\brief Test case: TC_osTimerStart_1
\details
  - Call osTimerStart to start the one-shot timer
  - Call osTimerStart to start the periodic timer
  - Call osTimerStart from ISR
  - Call osTimerStart with invalid ticks value
  - Call osTimerStart with null object
*/
void TC_osTimerStart_1 (void) {
#if (TC_OSTIMERSTART_1_EN)
  osTimerId_t id;
  uint32_t arg = 1U;

  Tim_Var_Os = 0U;

  /* Create a one-shot timer */
  id = osTimerNew (&TimCb_Oneshot, osTimerOnce, &arg, NULL);
  ASSERT_TRUE (id != NULL);

  /* Call osTimerStart to start the one-shot timer */
  ASSERT_TRUE (osTimerStart (id, 2U) == osOK);

  /* Wait until timer expires */
  osDelay(10U);

  /* Check if the timer callback function was called */
  ASSERT_TRUE (Tim_Var_Os == 1U);

  /* Delete the timer */
  osTimerDelete (id);


  Tim_Var_Per = 0U;

  /* Create a periodic timer */
  id = osTimerNew (&TimCb_Periodic, osTimerPeriodic, &arg, NULL);
  ASSERT_TRUE (id != NULL);

  /* Call osTimerStart to start the periodic timer */
  ASSERT_TRUE (osTimerStart (id, 2U) == osOK);

  /* Wait until timer expires */
  osDelay(10U);

  /* Check if the timer callback function was called multiple times */
  ASSERT_TRUE (Tim_Var_Per == 5U);

  /* Delete the timer */
  osTimerDelete (id);


  /* Create a one-shot timer */
  id = osTimerNew (&TimCb_Oneshot, osTimerOnce, &arg, NULL);
  ASSERT_TRUE (id != NULL);

  /* Call osTimerStart from ISR */
  TST_IRQHandler = Irq_osTimerStart_1;
  Isr_osStatus = osOK;
  TimerId = id;
  SetPendingIRQ(IRQ_A);
  ASSERT_TRUE (Isr_osStatus == osErrorISR);

  /* Call osTimerStart with invalid ticks value */
  ASSERT_TRUE (osTimerStart (id, 0U) == osErrorParameter);

  /* Delete the timer */
  osTimerDelete (id);

  /* Call osTimerStart with null object */
  ASSERT_TRUE (osTimerStart (NULL, 10U) == osErrorParameter);
#endif
}

/*-----------------------------------------------------------------------------
 * TC_osTimerStart_1: ISR handler
 *----------------------------------------------------------------------------*/
#if (TC_OSTIMERSTART_1_EN)
void Irq_osTimerStart_1 (void) {
  Isr_osStatus = osTimerStart (TimerId, 10U);
}
#endif

/*=======0=========1=========2=========3=========4=========5=========6=========7=========8=========9=========0=========1====*/
/**
\brief Test case: TC_osTimerStart_2
\details
  - Call osTimerStart from one-shot timer callback to re-start the timer
*/
void TC_osTimerStart_2 (void) {
#if (TC_OSTIMERSTART_2_EN)
  osTimerId_t id;

  Tim_Var_Os  = 0U;
  Cb_osStatus = osError;

  /* Create a one-shot timer */
  id = osTimerNew (&TimCb_osTimerStart_2, osTimerOnce, &id, NULL);
  ASSERT_TRUE (id != NULL);

  /* Call osTimerStart to start the one-shot timer */
  ASSERT_TRUE (osTimerStart (id, 2U) == osOK);

  /* Wait until timer expires */
  osDelay(3U);

  /* Check if the timer callback function was called */
  ASSERT_TRUE (Tim_Var_Os == 1U);

  /* Check if the timer was re-started */
  ASSERT_TRUE (Cb_osStatus == osOK);
  ASSERT_TRUE (osTimerIsRunning (id) == 1U);

  /* Wait until timer expires */
  osDelay(5U);

  /* Check if the timer callback function was called */
  ASSERT_TRUE (Tim_Var_Os == 2U);

  /* Delete the timer */
  osTimerDelete (id);
#endif
}

/*-----------------------------------------------------------------------------
 * TC_osTimerStart_2: Timer callback
 *----------------------------------------------------------------------------*/
#if (TC_OSTIMERSTART_2_EN)
void TimCb_osTimerStart_2  (void *arg) {
  osTimerId_t id = *(osTimerId_t *)arg;

  Tim_Var_Os += 1U;

  Cb_osStatus = osTimerStart (id, 4U);
}
#endif

/*=======0=========1=========2=========3=========4=========5=========6=========7=========8=========9=========0=========1====*/
/**
\brief Test case: TC_osTimerStop_1
\details
  - Call osTimerStop to stop the one-shoot timer
  - Call osTimerStop to stop the periodic timer
  - Call osTimerStop from ISR
  - Call osTimerStop with null object
*/
void TC_osTimerStop_1 (void) {
#if (TC_OSTIMERSTOP_1_EN)
  osTimerId_t id;
  uint32_t arg = 1U;

  /* Create one shot timer */
  id = osTimerNew (&TimCb_Oneshot, osTimerOnce, &arg, NULL);
  ASSERT_TRUE (id != NULL);

  /* Start timer */
  osTimerStart (id, 10U);

  /* Call osTimerStop to stop the one-shoot timer */
  ASSERT_TRUE (osTimerStop (id) == osOK);

  /* Delete timer */
  osTimerDelete (id);


  /* Create periodic timer */
  id = osTimerNew (&TimCb_Periodic, osTimerPeriodic, &arg, NULL);
  ASSERT_TRUE (id != NULL);

  /* Start the timer */
  osTimerStart (id, 10U);

  /* Call osTimerStop to stop the periodic timer */
  ASSERT_TRUE (osTimerStop (id) == osOK);

  /* Delete timer */
  osTimerDelete (id);


  /* Create one shot timer */
  id = osTimerNew (&TimCb_Oneshot, osTimerOnce, &arg, NULL);
  ASSERT_TRUE (id != NULL);

  /* Start the timer */
  osTimerStart (id, 10U);

  /* Call osTimerStop from ISR */
  TST_IRQHandler = Irq_osTimerStop_1;
  Isr_osStatus = osOK;
  TimerId = id;
  SetPendingIRQ(IRQ_A);
  ASSERT_TRUE (Isr_osStatus == osErrorISR);

  /* Delete the timer */
  osTimerDelete (id);

  /* Call osTimerStop with null object */
  ASSERT_TRUE (osTimerStop (NULL) == osErrorParameter);
#endif
}

/*-----------------------------------------------------------------------------
 * TC_osTimerStop_1: ISR handler
 *----------------------------------------------------------------------------*/
#if (TC_OSTIMERSTOP_1_EN)
void Irq_osTimerStop_1 (void) {
  Isr_osStatus = osTimerStop (TimerId);
}
#endif

/*=======0=========1=========2=========3=========4=========5=========6=========7=========8=========9=========0=========1====*/
/**
\brief Test case: TC_osTimerStop_2
\details
  - Call osTimerStop to stop already stopped one-shoot timer
  - Call osTimerStop to stop already stopped periodic timer
*/
void TC_osTimerStop_2 (void) {
#if (TC_OSTIMERSTOP_2_EN)
  osTimerId_t id;
  uint32_t arg = 1U;

  /* Create one shot timer */
  id = osTimerNew (&TimCb_Oneshot, osTimerOnce, &arg, NULL);
  ASSERT_TRUE (id != NULL);

  /* Start timer */
  osTimerStart (id, 10U);

  /* Call osTimerStop to stop the one-shoot timer */
  ASSERT_TRUE (osTimerStop (id) == osOK);

  /* Call osTimerStop to stop already stopped one-shoot timer */
  ASSERT_TRUE (osTimerStop (id) == osErrorResource);

  /* Delete timer */
  osTimerDelete (id);


  /* Create periodic timer */
  id = osTimerNew (&TimCb_Periodic, osTimerPeriodic, &arg, NULL);
  ASSERT_TRUE (id != NULL);

  /* Start the timer */
  osTimerStart (id, 10U);

  /* Call osTimerStop to stop the periodic timer */
  ASSERT_TRUE (osTimerStop (id) == osOK);

  /* Call osTimerStop to stop already stopped periodic timer */
  ASSERT_TRUE (osTimerStop (id) == osErrorResource);

  /* Delete timer */
  osTimerDelete (id);
#endif
}

/*=======0=========1=========2=========3=========4=========5=========6=========7=========8=========9=========0=========1====*/
/**
\brief Test case: TC_osTimerIsRunning_1
\details
  - Call osTimerIsRunning to check whether a one-shoot timer is running
  - Call osTimerIsRunning to check whether a one-shoot timer is stopped
  - Call osTimerIsRunning to check whether a periodic timer is running
  - Call osTimerIsRunning to check whether a periodic timer is stopped
  - Call osTimerIsRunning from ISR
  - Call osTimerIsRunning with null object
*/
void TC_osTimerIsRunning_1 (void) {
#if (TC_OSTIMERISRUNNING_1_EN)
  osTimerId_t id;
  uint32_t arg = 1U;

  /* Create one shot timer */
  id = osTimerNew (&TimCb_Oneshot, osTimerOnce, &arg, NULL);
  ASSERT_TRUE (id != NULL);

  /* Start timer */
  osTimerStart (id, 10U);

  /* Call osTimerIsRunning to check whether a one-shoot timer is running */
  ASSERT_TRUE (osTimerIsRunning (id) == 1U);

  /* Call osTimerStop to stop the one-shoot timer */
  ASSERT_TRUE (osTimerStop (id) == osOK);

  /* Call osTimerIsRunning to check whether a one-shoot timer is stopped */
  ASSERT_TRUE (osTimerIsRunning (id) == 0U);

  /* Delete timer */
  osTimerDelete (id);


  /* Create periodic timer */
  id = osTimerNew (&TimCb_Periodic, osTimerPeriodic, &arg, NULL);
  ASSERT_TRUE (id != NULL);

  /* Start the timer */
  osTimerStart (id, 10U);

  /* Call osTimerIsRunning to check whether a periodic timer is running */
  ASSERT_TRUE (osTimerIsRunning (id) == 1U);

  /* Call osTimerStop to stop the periodic timer */
  ASSERT_TRUE (osTimerStop (id) == osOK);

  /* Call osTimerIsRunning to check whether a periodic timer is stopped */
  ASSERT_TRUE (osTimerIsRunning (id) == 0U);

  /* Delete timer */
  osTimerDelete (id);


  /* Create one shot timer */
  id = osTimerNew (&TimCb_Oneshot, osTimerOnce, &arg, NULL);
  ASSERT_TRUE (id != NULL);

  /* Call osTimerIsRunning from ISR */
  TST_IRQHandler = Irq_osTimerIsRunning_1;
  Isr_u32 = 1U;
  TimerId = id;
  SetPendingIRQ(IRQ_A);
  ASSERT_TRUE (Isr_u32 == 0U);

  /* Delete the timer */
  osTimerDelete (id);

  /* Call osTimerIsRunning with null object */
  ASSERT_TRUE (osTimerIsRunning (NULL) == 0U);
#endif
}

/*-----------------------------------------------------------------------------
 * TC_osTimerIsRunning_1: ISR handler
 *----------------------------------------------------------------------------*/
#if (TC_OSTIMERISRUNNING_1_EN)
void Irq_osTimerIsRunning_1 (void) {
  Isr_u32 = osTimerIsRunning (TimerId);
}
#endif

/*=======0=========1=========2=========3=========4=========5=========6=========7=========8=========9=========0=========1====*/
/**
\brief Test case: TC_osTimerDelete_1
\details
  - Call osTimerDelete to delete stopped one-shoot timer
  - Call osTimerDelete to delete running one-shoot timer
  - Call osTimerDelete to delete stopped periodic timer
  - Call osTimerDelete to delete running periodic timer
  - Call osTimerDelete from ISR
  - Call osTimerDelete with null object
*/
void TC_osTimerDelete_1 (void) {
#if (TC_OSTIMERDELETE_1_EN)
  osTimerId_t id;
  uint32_t arg = 1U;

  /* Create one shot timer */
  id = osTimerNew (&TimCb_Oneshot, osTimerOnce, &arg, NULL);
  ASSERT_TRUE (id != NULL);

  /* Call osTimerDelete to delete stopped one-shoot timer */
  ASSERT_TRUE (osTimerDelete (id) == osOK);

  /* Create one shot timer */
  id = osTimerNew (&TimCb_Oneshot, osTimerOnce, &arg, NULL);
  ASSERT_TRUE (id != NULL);

  /* Start timer */
  osTimerStart (id, 10U);

  /* Call osTimerDelete to delete running one-shoot timer */
  ASSERT_TRUE (osTimerDelete (id) == osOK);


  /* Create periodic timer */
  id = osTimerNew (&TimCb_Periodic, osTimerPeriodic, &arg, NULL);
  ASSERT_TRUE (id != NULL);

  /* Call osTimerDelete to delete stopped periodic timer */
  ASSERT_TRUE (osTimerDelete (id) == osOK);

  /* Create periodic timer */
  id = osTimerNew (&TimCb_Periodic, osTimerPeriodic, &arg, NULL);
  ASSERT_TRUE (id != NULL);

  /* Start the timer */
  osTimerStart (id, 10U);

  /* Call osTimerDelete to delete running periodic timer */
  ASSERT_TRUE (osTimerDelete (id) == osOK);


  /* Create one shot timer */
  id = osTimerNew (&TimCb_Oneshot, osTimerOnce, &arg, NULL);
  ASSERT_TRUE (id != NULL);

  /* Call osTimerDelete from ISR */
  TST_IRQHandler = Irq_osTimerDelete_1;
  Isr_osStatus = osOK;
  TimerId = id;
  SetPendingIRQ(IRQ_A);
  ASSERT_TRUE (Isr_osStatus == osErrorISR);

  /* Delete the timer */
  osTimerDelete (id);

  /* Call osTimerDelete with null object */
  ASSERT_TRUE (osTimerDelete (NULL) == osErrorParameter);
#endif
}

/*-----------------------------------------------------------------------------
 * TC_osTimerDelete_1: ISR handler
 *----------------------------------------------------------------------------*/
#if (TC_OSTIMERDELETE_1_EN)
void Irq_osTimerDelete_1 (void) {
  Isr_osStatus = osTimerDelete (TimerId);
}
#endif

/*=======0=========1=========2=========3=========4=========5=========6=========7=========8=========9=========0=========1====*/
/**
\brief Test case: TC_TimerOneShot
\details
- Create a one shot timer
- Ensure timer is not running
- Start timer and check that callback was called only once
- Ensure correct status reporting
- Delete the timer
*/
void TC_TimerOneShot (void) {
#if (TC_TIMERONESHOT_EN)
  uint32_t i, var = 1;
  osTimerId_t id;

  /* - Create a one shot timer */
  id = osTimerNew ((osTimerFunc_t)&TimCb_Oneshot, osTimerOnce, &var, NULL);
  ASSERT_TRUE (id != NULL);

  if (id) {
    /* - Ensure timer is not running */
    ASSERT_TRUE (osTimerIsRunning (id) == 0);
    ASSERT_TRUE (osTimerStop (id) == osErrorResource);

    Tim_Var_Os = 0U;

    /* - Start timer and check that callback was called only once */
    ASSERT_TRUE (osTimerStart (id, 10U) == osOK);
    ASSERT_TRUE (osTimerIsRunning (id) == 1);
    
    /* Wait for timer interval */
    for (i = 20U; i; i--) {
      if (Tim_Var_Os > 0U) {
        break;
      }
      osDelay(1U);
    }
    ASSERT_TRUE (i > 0);
    ASSERT_TRUE (Tim_Var_Os == 1U);
    
    /* Wait another interval */
    for (i = 20U; i; i--) {
      if (Tim_Var_Os > 1U) {
        break;
      }
      osDelay(1);
    }
    ASSERT_TRUE (i == 0);
    ASSERT_TRUE (Tim_Var_Os == 1U);

    /* - Ensure correct status reporting */
    ASSERT_TRUE (osTimerStop (id) == osErrorResource);
    /* - Delete the timer */
    ASSERT_TRUE (osTimerDelete (id) == osOK);
  }
#endif
}

/*=======0=========1=========2=========3=========4=========5=========6=========7=========8=========9=========0=========1====*/
/**
\brief Test case: TC_TimerPeriodic
\details
- Create a periodic timer
- Ensure timer is not running
- Start timer and check if callback function is called more than once
- Stop the timer
- Ensure correct status reporting
- Delete the timer
*/
void TC_TimerPeriodic (void) {
#if (TC_TIMERPERIODIC_EN)
  uint32_t i, var = 1;
  osTimerId_t id;

  /* - Create a periodic timer */
  id = osTimerNew ((osTimerFunc_t)&TimCb_Periodic, osTimerPeriodic, &var, NULL);
  ASSERT_TRUE (id != NULL);

  if (id) {
    /* - Ensure timer is not running */
    ASSERT_TRUE (osTimerIsRunning (id) == 0);
    ASSERT_TRUE (osTimerStop (id) == osErrorResource);
    
    /* - Start timer and check if callback function is called more than once */
    ASSERT_TRUE (osTimerStart (id, 10) == osOK);
    ASSERT_TRUE (osTimerIsRunning (id) == 1);
    
    /* Wait for timer interval */
    for (i = 40; i; i--) {
      if (Tim_Var_Per > 2) {
        break;
      }
      osDelay(1);
    }
    ASSERT_TRUE (i != 0);
    ASSERT_TRUE (Tim_Var_Per > 2);
    
    /* - Stop the timer */
    ASSERT_TRUE (osTimerStop (id) == osOK);
    /* - Ensure correct status reporting */
    ASSERT_TRUE (osTimerStop (id) == osErrorResource);
    /* - Delete the timer */
    ASSERT_TRUE (osTimerDelete (id) == osOK);
  }
#endif
}

/*=======0=========1=========2=========3=========4=========5=========6=========7=========8=========9=========0=========1====*/
/**
\brief Test case: TC_TimerAllocation
\details
- Test timer object allocation
*/
void TC_TimerAllocation (void) {
#if (TC_TIMERALLOCATION_EN)
  osTimerId_t id[MAX_TIMER_NUM];
  uint32_t cnt = 0U;
  uint32_t max = 0U;
  uint32_t i;
  
  /* Create max number of objects */
  for (i = 0U; i < MAX_TIMER_NUM; i++) {
    id[i] = osTimerNew ((osTimerFunc_t)&TimCb_Oneshot, osTimerOnce, NULL, NULL);

    if (id[i] == NULL) {
      max = i;
      break;
    }
  }
  ASSERT_TRUE (i > 0U);

  if (max > 0U) {
    /* Try to allocate extra object */
    ASSERT_TRUE(osTimerNew ((osTimerFunc_t)&TimCb_Oneshot, osTimerOnce, NULL, NULL) == NULL);
  }

  osDelay(10);

  /* Delete all*/
  cnt = i;

  for (i = 0U; i < cnt; i++) {
    ASSERT_TRUE(osTimerDelete(id[i]) == osOK);
  }
#endif
}

/**
@}
*/ 
// end of group timer_func
