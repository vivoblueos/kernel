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

#include <stdbool.h>
#include <string.h>
#include "cmsis_rv2.h"

/*-----------------------------------------------------------------------------
 *      Test implementation
 *----------------------------------------------------------------------------*/
#define MAX_EVFLAGS_NUM  64

#define EVENT_FLAGS_MSK ((1U << MAX_EVENTFLAGS_CNT) - 1)

void Th_EventFlags_0       (void *arg);
void Th_EventFlags_1       (void *arg);
void Th_EventFlagsSet      (void *arg);
void Th_EventFlagsWakeup   (void *arg);
void Th_EventFlagsWait     (void *arg);
void Th_osEventFlagsWait_1 (void *arg);

void Irq_osEventFlagsNew_1     (void);
void Irq_osEventFlagsSet_1     (void);
void Irq_osEventFlagsClear_1   (void);
void Irq_osEventFlagsGet_1     (void);
void Irq_osEventFlagsWait_1    (void);
void Irq_osEventFlagsDelete_1  (void);
void Irq_osEventFlagsGetName_1 (void);

/*-----------------------------------------------------------------------------
 * Event flags setting thread
 *----------------------------------------------------------------------------*/
void Th_EventFlagsSet (void *arg) {
  uint32_t flags = *(uint32_t *)arg;
  osEventFlagsSet (EventFlagsId, flags);

  /* Explicitly terminate this thread */
  osThreadTerminate (osThreadGetId());
}

/*-----------------------------------------------------------------------------
 * Wakeup thread
 *----------------------------------------------------------------------------*/
void Th_EventFlagsWakeup (void __attribute__((unused)) *arg)
{
  osDelay(10);
  /* Send signal back to the main thread */
  ASSERT_TRUE (osEventFlagsSet (EventFlagsId, 1U) == 0U);

  /* Explicitly terminate this thread */
  osThreadTerminate (osThreadGetId());
}

/*-----------------------------------------------------------------------------
 * Wait event flag thread
 *----------------------------------------------------------------------------*/
void Th_EventFlagsWait (void __attribute__((unused)) *arg)
{
  /* Wait event flag */
  osEventFlagsWait (EventFlagsId, 1U, osFlagsWaitAll, osWaitForever);

  /* Explicitly terminate this thread */
  osThreadTerminate (osThreadGetId());
}


/*-----------------------------------------------------------------------------
 * Th_EventFlags thread 0
 *----------------------------------------------------------------------------*/
void Th_EventFlags_0 (void *arg) {
  osEventFlagsId_t id[2];
  uint32_t flags;
  uint32_t flag;

  id[0] = ((osEventFlagsId_t *)arg)[0];
  id[1] = ((osEventFlagsId_t *)arg)[1];

  flag = 1U;
  do {
    /* - Send signal mask to Th_EventFlags_1 */
    osEventFlagsSet (id[0], flag);
    /* - Wait for signals sent from Th_EventFlags_1 */
    flags = osEventFlagsWait (id[1], flag, 0, 100);
    ASSERT_TRUE (flags > 0U);

    flag <<= 1;
    flag  |= (flag & 2U) ? (0U) : (1U);
  }
  while ((flags > 0U) && (flag <= EVENT_FLAGS_MSK));

  osEventFlagsSet (EventFlagsId, 1U);

  /* Explicitly terminate this thread */
  osThreadTerminate (osThreadGetId());
}

/*-----------------------------------------------------------------------------
 * Th_EventFlags thread 1
 *----------------------------------------------------------------------------*/
void Th_EventFlags_1 (void *arg) {
  osEventFlagsId_t id[2];
  uint32_t flags;
  uint32_t flag;

  id[0] = ((osEventFlagsId_t *)arg)[0];
  id[1] = ((osEventFlagsId_t *)arg)[1];

  flag = 1U;
  do {
    /* - Wait for signals sent from Th_EventFlags_0 */
    flags = osEventFlagsWait (id[0], flag, 0, 100);
    ASSERT_TRUE (flags > 0U);

    /* - Send received signal mask back to Th_EventFlags_0 */
    osEventFlagsSet (id[1], flag);

    flag <<= 1;
    flag  |= (flag & 2U) ? (0U) : (1U);
  }
  while ((flags > 0U) && (flag <= EVENT_FLAGS_MSK));

  osEventFlagsSet (EventFlagsId, 2U);

  /* Explicitly terminate this thread */
  osThreadTerminate (osThreadGetId());
}


/*-----------------------------------------------------------------------------
 *      Test cases
 *----------------------------------------------------------------------------*/

/*=======0=========1=========2=========3=========4=========5=========6=========7=========8=========9=========0=========1====*/
/**
\defgroup eventflags_funcs Event Flags Functions
\brief Event Flags Functions Test Cases
\details
The test cases check the Event Flags functions.

@{
*/

/*=======0=========1=========2=========3=========4=========5=========6=========7=========8=========9=========0=========1====*/
/**
\brief Test case: TC_osEventFlagsNew_1
\details
  - Call osEventFlagsNew to create event flags object
  - Call osEventFlagsNew from ISR
*/
void TC_osEventFlagsNew_1 (void) {
#if (TC_OSEVENTFLAGSNEW_1_EN)
  osEventFlagsId_t id;

  /* Call osEventFlagsNew to create event flags object */
  id = osEventFlagsNew (NULL);
  ASSERT_TRUE (id != NULL);

  /* Delete created event flags */
  ASSERT_TRUE (osEventFlagsDelete(id) == osOK);

  /* Call osEventFlags from ISR */
  TST_IRQHandler = Irq_osEventFlagsNew_1;
  EventFlagsId = (osEventFlagsId_t)(-1);
  SetPendingIRQ(IRQ_A);
  ASSERT_TRUE (EventFlagsId == NULL);
#endif
}

/*-----------------------------------------------------------------------------
 * TC_osEventFlagsNew_1: ISR handler
 *----------------------------------------------------------------------------*/
#if (TC_OSEVENTFLAGSNEW_1_EN)
void Irq_osEventFlagsNew_1 (void) {
  EventFlagsId = osEventFlagsNew (NULL);
}
#endif

/*=======0=========1=========2=========3=========4=========5=========6=========7=========8=========9=========0=========1====*/
/**
\brief Test case: TC_osEventFlagsNew_2
\details
  - Call osEventFlagsNew to create event flags object and assign a name to it
*/
void TC_osEventFlagsNew_2 (void) {
#if (TC_OSEVENTFLAGSNEW_2_EN)
  osEventFlagsAttr_t attr = {NULL, 0U, NULL, 0U};
  osEventFlagsId_t id;

  /* Call osEventFlags to create event flags object and assign a name to it */
  attr.name = "EventFlags";

  id = osEventFlagsNew (&attr);
  ASSERT_TRUE (id != NULL);

  /* Delete created event flags */
  ASSERT_TRUE (osEventFlagsDelete(id) == osOK);
#endif
}

/*=======0=========1=========2=========3=========4=========5=========6=========7=========8=========9=========0=========1====*/
/**
\brief Test case: TC_osEventFlagsNew_3
\details
  - Call osEventFlagsNew to create event flags object by specifying memory for control block in attributes
*/
void TC_osEventFlagsNew_3 (void) {
#if (TC_OSEVENTFLAGSNEW_3_EN)
  osEventFlagsAttr_t attr = {NULL, 0U, NULL, 0U};
  osEventFlagsId_t id;

  /* Call osEventFlagsNew to create event flags object by specifying memory for control block in attributes */
  attr.cb_mem  = &EventFlags_CbMem;
  attr.cb_size = sizeof(EventFlags_CbMem);

  id = osEventFlagsNew (&attr);
  ASSERT_TRUE (id != NULL);

  /* Delete created event flags */
  ASSERT_TRUE (osEventFlagsDelete(id) == osOK);
#endif
}

/*=======0=========1=========2=========3=========4=========5=========6=========7=========8=========9=========0=========1====*/
/**
\brief Test case: TC_osEventFlagsSet_1
\details
  - Call osEventFlagsSet to set all available flags in event flags object
  - Call osEventFlagsSet from ISR
*/
void TC_osEventFlagsSet_1 (void) {
#if (TC_OSEVENTFLAGSSET_1_EN)
  osEventFlagsId_t id;
  uint32_t flags, set, rflags;

  /* Create event flags object */
  id = osEventFlagsNew(NULL);
  ASSERT_TRUE(id != NULL);

  /* Set all flags */
  flags = 0U;
  set   = 1U;
  do {
    flags = (flags << 1U) | 1U;
    /* Call osEventFlagsSet to set all available flags in event flags object */
    rflags = osEventFlagsSet (id, set);
    ASSERT_TRUE (rflags == flags);
    set   = set << 1U;
  }
  while ((rflags == flags) && (set <= EVENT_FLAGS_MSK));

  /* Delete event flags object */
  ASSERT_TRUE (osEventFlagsDelete (id) == osOK);

  /* Create event flags object */
  id = osEventFlagsNew(NULL);
  ASSERT_TRUE(id != NULL);

  /* Call osEventFlagsSet from ISR */
  TST_IRQHandler = Irq_osEventFlagsSet_1;
  EventFlagsId = id;
  SetPendingIRQ(IRQ_A);

  /* Delete event flags object */
  ASSERT_TRUE (osEventFlagsDelete (id) == osOK);

  /* Call osEventFlagsSet with null object */
  ASSERT_TRUE (osEventFlagsSet (NULL, 1U) == (uint32_t)osErrorParameter);
#endif
}

/*-----------------------------------------------------------------------------
 * TC_osEventFlagsSet_1: ISR handler
 *----------------------------------------------------------------------------*/
#if (TC_OSEVENTFLAGSSET_1_EN)
void Irq_osEventFlagsSet_1 (void) {
  uint32_t flags, set, rflags;

  /* Set all flags */
  flags = 0U;
  set   = 1U;
  do {
    flags = (flags << 1U) | 1U;
    /* Call osEventFlagsSet to set all available flags in event flags object */
    rflags = osEventFlagsSet (EventFlagsId, set);
    ASSERT_TRUE (rflags == flags);
    set   = set << 1U;
  }
  while ((rflags == flags) && (set <= EVENT_FLAGS_MSK));
}
#endif

/*=======0=========1=========2=========3=========4=========5=========6=========7=========8=========9=========0=========1====*/
/**
\brief Test case: TC_osEventFlagsClear_1
\details
  - Call osEventFlagsClear to clear all available flags in event flags object
  - Call osEventFlagsClear from ISR
  - Call osEventFlagsClear with null object
*/
void TC_osEventFlagsClear_1 (void) {
#if (TC_OSEVENTFLAGSCLEAR_1_EN)
  osEventFlagsId_t id;
  uint32_t flags, clr, rflags;

  /* Create event flags object */
  id = osEventFlagsNew(NULL);
  ASSERT_TRUE(id != NULL);

  /* Set all available flags */
  osEventFlagsSet (id, EVENT_FLAGS_MSK);

  flags = EVENT_FLAGS_MSK;
  clr   = 1U;
  while ((clr & EVENT_FLAGS_MSK) != 0U) {
    /* Call osEventFlagsClear to clear all available flags in event flags object */
    rflags = osEventFlagsClear (id, clr);
    if (ASSERT_TRUE (rflags == flags) == false) {
      break;
    }
    clr   = (clr   << 1U);
    flags = (flags << 1U) & EVENT_FLAGS_MSK;
  }

  /* Delete event flags object */
  ASSERT_TRUE (osEventFlagsDelete (id) == osOK);

  /* Create event flags object */
  id = osEventFlagsNew(NULL);
  ASSERT_TRUE(id != NULL);

  /* Set all available flags */
  osEventFlagsSet (id, EVENT_FLAGS_MSK);

  /* Call osEventFlagsClear from ISR */
  TST_IRQHandler = Irq_osEventFlagsClear_1;
  EventFlagsId = id;
  SetPendingIRQ(IRQ_A);

  /* Delete event flags object */
  ASSERT_TRUE (osEventFlagsDelete (id) == osOK);

  /* Call osEventFlagsClear with null object */
  ASSERT_TRUE (osEventFlagsClear (NULL, 0x10000000U) == osFlagsErrorParameter);
#endif
}

/*-----------------------------------------------------------------------------
 * TC_osEventFlagsClear_1: ISR handler
 *----------------------------------------------------------------------------*/
#if (TC_OSEVENTFLAGSCLEAR_1_EN)
void Irq_osEventFlagsClear_1 (void) {
  uint32_t flags, clr, rflags;

  flags = EVENT_FLAGS_MSK;
  clr   = 1U;
  while ((clr & EVENT_FLAGS_MSK) != 0U) {
    /* Call osEventFlagsClear to clear all available flags in event flags object */
    rflags = osEventFlagsClear (EventFlagsId, clr);
    if (ASSERT_TRUE (rflags == flags) == false) {
      break;
    }
    clr   = (clr   << 1U);
    flags = (flags << 1U) & EVENT_FLAGS_MSK;
  }
}
#endif

/*=======0=========1=========2=========3=========4=========5=========6=========7=========8=========9=========0=========1====*/
/**
\brief Test case: TC_osEventFlagsGet_1
\details
  - Call osEventFlagsGet to retrieve the flags in event flags object when all flags are cleared
  - Call osEventFlagsGet to retrieve the flags in event flags object when all flags are set
  - Call osEventFlagsGet from ISR
  - Call osEventFlagsGet with null object
*/
void TC_osEventFlagsGet_1 (void) {
#if (TC_OSEVENTFLAGSGET_1_EN)
  osEventFlagsId_t id;

  /* Create event flags object */
  id = osEventFlagsNew(NULL);
  ASSERT_TRUE(id != NULL);

  /* Call osEventFlagsGet to retrieve the flags in event flags object when all flags are cleared */
  ASSERT_TRUE (osEventFlagsGet (id) == 0U);

  /* Set all available flags */
  osEventFlagsSet (id, EVENT_FLAGS_MSK);

  /* Call osEventFlagsGet to retrieve the flags in event flags object when all flags are set */
  ASSERT_TRUE (osEventFlagsGet (id) == EVENT_FLAGS_MSK);

  /* Delete event flags object */
  ASSERT_TRUE (osEventFlagsDelete (id) == osOK);

  /* Create event flags object */
  id = osEventFlagsNew(NULL);
  ASSERT_TRUE(id != NULL);

  /* Set flags of random pattern */
  osEventFlagsSet (id, 0x55AA55AA & EVENT_FLAGS_MSK);

  /* Call osEventFlagsGet from ISR */
  TST_IRQHandler = Irq_osEventFlagsGet_1;
  EventFlagsId = id;
  SetPendingIRQ(IRQ_A);

  /* Delete event flags object */
  ASSERT_TRUE (osEventFlagsDelete (id) == osOK);

  /* Call osEventFlagsGet with null object */
  ASSERT_TRUE (osEventFlagsGet (NULL) == 0U);
#endif
}

/*-----------------------------------------------------------------------------
 * TC_osEventFlagsGet_1: ISR handler
 *----------------------------------------------------------------------------*/
#if (TC_OSEVENTFLAGSGET_1_EN)
void Irq_osEventFlagsGet_1 (void) {
  ASSERT_TRUE (osEventFlagsGet(EventFlagsId) == (0x55AA55AA & EVENT_FLAGS_MSK));
}
#endif

/*=======0=========1=========2=========3=========4=========5=========6=========7=========8=========9=========0=========1====*/
/**
\brief Test case: TC_osEventFlagsWait_1
\details
  - Call osEventFlagsWait without timeout to retrieve the event flags
  - Call osEventFlagsWait with timeout to retrieve the event flags
  - Call osEventFlagsWait from ISR with timeout
  - Call osEventFlagsWait from ISR without timeout
  - Call osEventFlagsWait with null object
  - Call osEventFlagsWait with the highest bit in flags set
*/
void TC_osEventFlagsWait_1 (void) {
#if (TC_OSEVENTFLAGSWAIT_1_EN)
  osThreadAttr_t attr = { NULL, osThreadDetached, NULL, 0U, NULL, 0U, osPriorityHigh, 0U, 0U};
  osEventFlagsId_t id;
  uint32_t cnt;

  /* Create event flags object */
  id = osEventFlagsNew(NULL);
  ASSERT_TRUE(id != NULL);

  EventFlagsId = id;
  cnt = 0U;

  /* Create a thread that shall wait for flags from EventFlagsId object */
  ThreadId = osThreadNew (Th_osEventFlagsWait_1, &cnt, &attr);
  ASSERT_TRUE (ThreadId != NULL);

  /* Check that the thread was started */
  ASSERT_TRUE (cnt == 1U);

  /* Set flags */
  osEventFlagsSet (id, 0x00000001U & EVENT_FLAGS_MSK);
  ASSERT_TRUE (cnt == 2U);
  osEventFlagsSet (id, 0x7FFFFFFFU & EVENT_FLAGS_MSK);
  ASSERT_TRUE (cnt == 3U);
  osEventFlagsSet (id, 0x2AAAAAAAU & EVENT_FLAGS_MSK);
  ASSERT_TRUE (cnt == 4U);
  osEventFlagsSet (id, 0x55555555U & EVENT_FLAGS_MSK);
  ASSERT_TRUE (cnt == 5U);

  /* Delete event flags object */
  ASSERT_TRUE (osEventFlagsDelete (id) == osOK);

  /* Create event flags object */
  id = osEventFlagsNew(NULL);
  ASSERT_TRUE(id != NULL);

  /* Set flags of random pattern */
  osEventFlagsSet (id, 0x55AA55AA & EVENT_FLAGS_MSK);

  /* Set flags of random pattern */
  osEventFlagsSet (id, 0x55AA55AA & EVENT_FLAGS_MSK);

  /* Call osEventFlagsWait from ISR (with and without timeout) */
  TST_IRQHandler = Irq_osEventFlagsWait_1;
  EventFlagsId = id;
  SetPendingIRQ(IRQ_A);
  ASSERT_TRUE (Isr_u32 == (0x55AA55AA & EVENT_FLAGS_MSK));

  /* Delete event flags object */
  ASSERT_TRUE (osEventFlagsDelete (id) == osOK);

  /* Call osEventFlagsWait with null object */
  ASSERT_TRUE (osEventFlagsWait (NULL, 0x55AA55AAU, osFlagsWaitAny, 0U) == osFlagsErrorParameter);

  /* Call osEventFlagsWait with the highest bit in flags set */
  ASSERT_TRUE (osEventFlagsWait (id, 0x80000000U, osFlagsWaitAny, 2U) == osFlagsErrorParameter);
  ASSERT_TRUE (osEventFlagsWait (id, 0x80000000U, osFlagsWaitAll, 2U) == osFlagsErrorParameter);
#endif
}

/*-----------------------------------------------------------------------------
 * TC_osEventFlagsWait_1: Helper thread
 *----------------------------------------------------------------------------*/
#if (TC_OSEVENTFLAGSWAIT_1_EN)
void Th_osEventFlagsWait_1 (void *arg) {
  uint32_t *cnt = (uint32_t *)arg;

  (*cnt)++;

  /* Wait event flag */
  Isr_u32 = osEventFlagsWait (EventFlagsId, 0x00000001U & EVENT_FLAGS_MSK, osFlagsWaitAll, osWaitForever);
  (*cnt)++;
  /* Wait event flag */
  Isr_u32 = osEventFlagsWait (EventFlagsId, 0x7FFFFFFFU & EVENT_FLAGS_MSK, osFlagsWaitAll, osWaitForever);
  (*cnt)++;
  /* Wait event flag */
  Isr_u32 = osEventFlagsWait (EventFlagsId, 0x2AAAAAAAU & EVENT_FLAGS_MSK, osFlagsWaitAll, osWaitForever);
  (*cnt)++;
  /* Wait event flag */
  Isr_u32 = osEventFlagsWait (EventFlagsId, 0x55555555U & EVENT_FLAGS_MSK, osFlagsWaitAll, osWaitForever);
  (*cnt)++;

  /* Terminate this thread */
  osThreadTerminate (osThreadGetId());
}
#endif

/*-----------------------------------------------------------------------------
 * TC_osEventFlagsWait_1: ISR handler
 *----------------------------------------------------------------------------*/
#if (TC_OSEVENTFLAGSWAIT_1_EN)
void Irq_osEventFlagsWait_1 (void) {
  ASSERT_TRUE (osEventFlagsWait (EventFlagsId, 0x55AA55AA & EVENT_FLAGS_MSK, osFlagsWaitAny, osWaitForever) == osFlagsErrorParameter);

  Isr_u32 = osEventFlagsWait (EventFlagsId, 0x55AA55AA & EVENT_FLAGS_MSK, osFlagsWaitAll, 0U);
}
#endif

/*=======0=========1=========2=========3=========4=========5=========6=========7=========8=========9=========0=========1====*/
/**
\brief Test case: TC_osEventFlagsDelete_1
\details
  - Call osEventFlagsDelete to delete a event flags object
  - Call osEventFlagsDelete from ISR
  - Call osEventFlagsDelete with null object
*/
void TC_osEventFlagsDelete_1 (void) {
#if (TC_OSEVENTFLAGSDELETE_1_EN)
  osEventFlagsId_t id;

  /* Create event flags object */
  id = osEventFlagsNew (NULL);
  ASSERT_TRUE (id != NULL);

  /* Call osEventFlagsDelete to delete a event flags object */
  ASSERT_TRUE (osEventFlagsDelete (id) == osOK);

  /* Create event flags object */
  id = osEventFlagsNew (NULL);
  ASSERT_TRUE (id != NULL);

  /* Call osEventFlagsDelete from ISR */
  TST_IRQHandler = Irq_osEventFlagsDelete_1;
  Isr_osStatus = osOK;
  EventFlagsId = id;
  SetPendingIRQ(IRQ_A);
  ASSERT_TRUE (Isr_osStatus == osErrorISR);

  /* Delete event flags object */
  ASSERT_TRUE (osEventFlagsDelete (id) == osOK);

  /* Call osEventFlagsDelete with null object */
  ASSERT_TRUE (osEventFlagsDelete (NULL) == osErrorParameter);
#endif
}

/*-----------------------------------------------------------------------------
 * TC_osEventFlagsDelete_1: ISR handler
 *----------------------------------------------------------------------------*/
#if (TC_OSEVENTFLAGSDELETE_1_EN)
void Irq_osEventFlagsDelete_1 (void) {
  Isr_osStatus = osEventFlagsDelete (EventFlagsId);
}
#endif

/*=======0=========1=========2=========3=========4=========5=========6=========7=========8=========9=========0=========1====*/
/**
\brief Test case: TC_osEventFlagsGetName_1
\details
  - Call osEventFlagsGetName to retrieve a name of an unnamed event flags
  - Call osEventFlagsGetName to retrieve a name of a event flags with assigned name
  - Call osEventFlagsGetName from ISR
  - Call osEventFlagsGetName with null object
*/
void TC_osEventFlagsGetName_1 (void) {
#if (TC_OSEVENTFLAGSGETNAME_1_EN)
  osEventFlagsAttr_t attr = {NULL, 0U, NULL, 0U};
  osEventFlagsId_t id;
  char const *name = "EventFlags";

  /* Create event flags object without assigned name */
  attr.name = NULL;
  id = osEventFlagsNew (&attr);
  ASSERT_TRUE (id != NULL);

  /* Call osEventFlagsGetName to retrieve a name of an unnamed event flags */
  ASSERT_TRUE(osEventFlagsGetName (id) == NULL);

  /* Delete event flags object */
  osEventFlagsDelete (id);


  /* Create event flags object with name assigned via attributes */
  attr.name = name;
  id = osEventFlagsNew (&attr);
  ASSERT_TRUE (id != NULL);

  /* Call osEventFlagsGetName to retrieve a name of a event flags with assigned name */
  ASSERT_TRUE (strcmp(osEventFlagsGetName(id), name) == 0U);

  /* Call osEventFlagsGetName from ISR */
  TST_IRQHandler = Irq_osEventFlagsGetName_1;
  EventFlagsId   = id;
  EventFlagsName = name;
  SetPendingIRQ(IRQ_A);
  ASSERT_TRUE (strcmp(EventFlagsName, name) == 0U);

  /* Delete event flags object */
  osEventFlagsDelete (id);

  /* Call osEventFlagsGetName with null object */
  ASSERT_TRUE (osEventFlagsGetName (NULL) == NULL);
#endif
}

/*-----------------------------------------------------------------------------
 * TC_osEventFlagsGetName_1: ISR handler
 *----------------------------------------------------------------------------*/
#if (TC_OSEVENTFLAGSGETNAME_1_EN)
void Irq_osEventFlagsGetName_1 (void) {
  EventFlagsName = osEventFlagsGetName (EventFlagsId);
}
#endif

/*=======0=========1=========2=========3=========4=========5=========6=========7=========8=========9=========0=========1====*/
/**
\brief Test case: TC_EventFlagsInterThreads
\details
- Create two child threads
  Within child thread:
- Verify that all flags are cleared
- Set all thread flags
- Verify that all thread flags are set
- Clear all thread flags
- Verify that all thread flags are cleared
*/
void TC_EventFlagsInterThreads (void) {
#if (TC_EVENTFLAGSINTERTHREADS_EN)
  osThreadAttr_t attr = { NULL, osThreadDetached, NULL, 0U, NULL, 0U, osPriorityBelowNormal, 0U, 0U};
  osEventFlagsId_t id[2];

  id[0] = osEventFlagsNew(NULL);
  ASSERT_TRUE (id[0] != NULL);

  id[1] = osEventFlagsNew(NULL);
  ASSERT_TRUE (id[1] != NULL);

  EventFlagsId = osEventFlagsNew(NULL);
  ASSERT_TRUE (EventFlagsId != NULL);

  /* Create child threads */
  ASSERT_TRUE (osThreadNew (Th_EventFlags_0, &id, &attr) != NULL);
  ASSERT_TRUE (osThreadNew (Th_EventFlags_1, &id, &attr) != NULL);

  /* Wait for event flags from child threads */
  ASSERT_TRUE (osEventFlagsWait (EventFlagsId, 0x03U, osFlagsWaitAll, 100) == 0x03U);

  /* Wait threads to terminate */
  osDelay(10);

  /* Delete event flags objects */
  ASSERT_TRUE (osEventFlagsDelete (id[0]) == osOK);
  ASSERT_TRUE (osEventFlagsDelete (id[1]) == osOK);
  ASSERT_TRUE (osEventFlagsDelete (EventFlagsId) == osOK);
#endif
}

/*=======0=========1=========2=========3=========4=========5=========6=========7=========8=========9=========0=========1====*/
/**
\brief Test case: TC_EventFlagsWaitTimeout
\details
- Clear all event flags for current thread
- Wait for any single event flag without timeout
- Wait for any single event flag with timeout
- Wait for all event flags without timeout
- Wait for all event flags with timeout
- Wait for various event flag masks from a signaling thread
*/
void TC_EventFlagsWaitTimeout (void) {
#if (TC_EVENTFLAGSWAITTIMEOUT_EN)
  osThreadAttr_t attr = { NULL, osThreadDetached, NULL, 0U, NULL, 0U, osPriorityBelowNormal, 0U, 0U};
  osThreadId_t id;
  uint32_t   flags;

  EventFlagsId = osEventFlagsNew(NULL);
  ASSERT_TRUE (EventFlagsId != NULL);

  if (EventFlagsId != NULL) {
    /* - Clear all signals for current thread */
    osEventFlagsClear (EventFlagsId, EVENT_FLAGS_MSK);

    /* - Wait for any single signal without timeout */
    ASSERT_TRUE (osEventFlagsWait (EventFlagsId, EVENT_FLAGS_MSK, osFlagsWaitAny, 0) == (uint32_t)osErrorResource);
    /* - Wait for any single signal with timeout */
    ASSERT_TRUE (osEventFlagsWait (EventFlagsId, EVENT_FLAGS_MSK, osFlagsWaitAny, 5) == (uint32_t)osErrorTimeout);
    /* - Wait for all signals without timeout */
    ASSERT_TRUE (osEventFlagsWait (EventFlagsId, EVENT_FLAGS_MSK, osFlagsWaitAll, 0) == (uint32_t)osErrorResource);
    /* - Wait for all signals with timeout */
    ASSERT_TRUE (osEventFlagsWait (EventFlagsId, EVENT_FLAGS_MSK, osFlagsWaitAll, 5) == (uint32_t)osErrorTimeout);

    /* - Create a signal setting thread */
    flags = 3U;
    id = osThreadNew (Th_EventFlagsSet, &flags, &attr);
    ASSERT_TRUE (id != NULL);

    if (id != NULL) {
      osDelay(5);

      /* - Wait for various signal masks from a signaling thread */
      ASSERT_TRUE (osEventFlagsWait (EventFlagsId, 1U, 0, 10) == 3U);
    }
    osDelay(10);

    /* - Create a signal setting thread */
    flags = 5U;
    id = osThreadNew (Th_EventFlagsSet, &flags, &attr);
    ASSERT_TRUE (id != NULL);

    if (id != NULL) {
      osDelay(5);

      /* - Wait for various signal masks from a signaling thread */
      ASSERT_TRUE (osEventFlagsWait (EventFlagsId, 2U, 0, 10) == 7U);
    }
    osEventFlagsClear (EventFlagsId, EVENT_FLAGS_MSK);
    osDelay(10);

    /* Delete event flags object */
    ASSERT_TRUE (osEventFlagsDelete (EventFlagsId) == osOK);
  }
#endif
}

/*=======0=========1=========2=========3=========4=========5=========6=========7=========8=========9=========0=========1====*/
/**
\brief Test case: TC_EventFlagsDeleteWaiting
\details
- Create a thread that waits for an event flag
- Delete event flags object
- Try to terminate thread
*/
void TC_EventFlagsDeleteWaiting (void) {
#if (TC_EVENTFLAGSDELETEWAITING_EN)
  osThreadAttr_t attr = { NULL, osThreadDetached, NULL, 0U, NULL, 0U, osPriorityAboveNormal, 0U, 0U};
  osThreadId_t id;
  osStatus_t stat;

  EventFlagsId = osEventFlagsNew(NULL);
  ASSERT_TRUE (EventFlagsId != NULL);

  if (EventFlagsId != NULL) {
    /* - Create a waiting thread */
    id = osThreadNew (Th_EventFlagsWait, NULL, &attr);
    ASSERT_TRUE (id != NULL);

    /* Delete event flags object */
    ASSERT_TRUE (osEventFlagsDelete (EventFlagsId) == osOK);

    /* Terminate thread */
    stat = osThreadTerminate (id);
    ASSERT_TRUE((stat == osErrorParameter)||(stat == osErrorResource));
  }
#endif
}
/*=======0=========1=========2=========3=========4=========5=========6=========7=========8=========9=========0=========1====*/
/**
\brief Test case: TC_EventFlagsCheckTimeout
\details
- Set time thresholds
- Create wakeup thread to set an event flag after 10 ticks
- Wait for an event flag with a defined timeout
- Check if the event flag is raised between the minimum and maximum thresholds
- Wait for an event flag with an infinite timeout
- Check if the event flag is raised between the minimum and maximum thresholds
*/
void TC_EventFlagsCheckTimeout (void) {
#if (TC_EVENTFLAGSCHECKTIMEOUT_EN)
  osThreadAttr_t attr = { NULL, osThreadDetached, NULL, 0U, NULL, 0U, osPriorityNormal, 0U, 0U};
  osThreadId_t id;
  uint32_t flags;
  uint32_t t_10;

  EventFlagsId = osEventFlagsNew(NULL);
  ASSERT_TRUE (EventFlagsId != NULL);

  if (EventFlagsId != NULL) {
    /* Synchronize tick */
    osDelay(1U);

    /* Create wakeup thread to set a signal after 10 ticks */
    id = osThreadNew(Th_EventFlagsWakeup, NULL, &attr);

    if (id != NULL) {
      t_10 = osKernelGetTickCount();
      flags = osEventFlagsWait (EventFlagsId, 1U, 0, 100);
      t_10 = osKernelGetTickCount() - t_10;

      ASSERT_TRUE (flags == 1U);
      ASSERT_TRUE (t_10 == 10U);
    }
    else {
      ASSERT_TRUE (id != NULL);
    }

    /* Wait until wakeup thread is terminated */
    osDelay(5U);

    /* Create wakeup thread to set a signal after 10 ticks */
    id = osThreadNew(Th_EventFlagsWakeup, NULL, &attr);

    if (id != NULL) {
      t_10 = osKernelGetTickCount();
      flags = osEventFlagsWait (EventFlagsId, 1U, 0, osWaitForever);
      t_10 = osKernelGetTickCount() - t_10;

      ASSERT_TRUE (flags == 1U);
      ASSERT_TRUE (t_10 == 10U);
    }
    else {
      ASSERT_TRUE (id != NULL);
    }

    /* Wait until wakeup thread is terminated */
    osDelay(5U);

    /* Delete event flags object */
    ASSERT_TRUE (osEventFlagsDelete (EventFlagsId) == osOK);
  }
#endif
}

/*=======0=========1=========2=========3=========4=========5=========6=========7=========8=========9=========0=========1====*/
/**
\brief Test case: TC_EventFlagsAllocation
\details
- Test event flags object allocation
*/
void TC_EventFlagsAllocation (void) {
#if (TC_EVENTFLAGSALLOCATION_EN)
  osEventFlagsId_t id[MAX_EVFLAGS_NUM];
  uint32_t cnt = 0U;
  uint32_t max = 0U;
  uint32_t i;

  /* Create max number of objects */
  for (i = 0U; i < MAX_EVFLAGS_NUM; i++) {
    id[i] = osEventFlagsNew(NULL);

    if (id[i] == NULL) {
      max = i;
      break;
    }
  }
  ASSERT_TRUE (i > 0U);

  if (max > 0U) {
    /* Try to allocate extra object */
    ASSERT_TRUE(osEventFlagsNew(NULL) == NULL);
  }

  osDelay(10U);

  /* Delete all */
  cnt = i;

  for (i = 0U; i < cnt; i++) {
    ASSERT_TRUE(osEventFlagsDelete(id[i]) == osOK);
  }
#endif
}

/**
@}
*/
// end of group threadflags_funcs
