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

#include <string.h>
#include "cmsis_rv2.h"

/*-----------------------------------------------------------------------------
 *      Test implementation
 *----------------------------------------------------------------------------*/
#define MAX_THREAD_NUM  64
#define MIN_THREAD_NUM   7

/* Definitions of shared variables */
static uint32_t Var_Counter;

void Th_CountingThread (void *arg);

/* Definitions for TC_ThreadNew */
static volatile uint32_t Var_ThreadExec;


void Th_Thr0 (void *arg);
void Th_Thr1 (void *arg);
void Th_Thr2 (void *arg);
void Th_Thr3 (void *arg);
void Th_Thr4 (void *arg);
void Th_Thr5 (void *arg);
void Th_Thr6 (void *arg);

/* TC_osThreadJoin_1: Helper threads */
void Th_Child_0   (void *arg);
void Th_Child_1   (void *arg);
void Th_Child_2   (void *arg);
void Th_Child_3   (void *arg);

static const osThreadAttr_t Th_Thr0_attr = { NULL, osThreadDetached, NULL, 0U, NULL, 0U, osPriorityLow,         0U, 0U};
static const osThreadAttr_t Th_Thr1_attr = { NULL, osThreadDetached, NULL, 0U, NULL, 0U, osPriorityBelowNormal, 0U, 0U};
static const osThreadAttr_t Th_Thr2_attr = { NULL, osThreadDetached, NULL, 0U, NULL, 0U, osPriorityNormal,      0U, 0U};
static const osThreadAttr_t Th_Thr3_attr = { NULL, osThreadDetached, NULL, 0U, NULL, 0U, osPriorityAboveNormal, 0U, 0U};
static const osThreadAttr_t Th_Thr4_attr = { NULL, osThreadDetached, NULL, 0U, NULL, 0U, osPriorityHigh,        0U, 0U};
static const osThreadAttr_t Th_Thr5_attr = { NULL, osThreadDetached, NULL, 0U, NULL, 0U, osPriorityRealtime,    0U, 0U};
static const osThreadAttr_t Th_Thr6_attr = { NULL, osThreadDetached, NULL, 0U, NULL, 0U, osPriorityError,       0U, 0U};

void Th_Thr0 (void *arg) { Var_ThreadExec += (arg == NULL) ? (1) : (2); osThreadTerminate (osThreadGetId()); }
void Th_Thr1 (void *arg) { Var_ThreadExec += (arg == NULL) ? (1) : (2); osThreadTerminate (osThreadGetId()); }
void Th_Thr2 (void *arg) { Var_ThreadExec += (arg == NULL) ? (1) : (2); osThreadTerminate (osThreadGetId()); }
void Th_Thr3 (void *arg) { Var_ThreadExec += (arg == NULL) ? (1) : (2); osThreadTerminate (osThreadGetId()); }
void Th_Thr4 (void *arg) { Var_ThreadExec += (arg == NULL) ? (1) : (2); osThreadTerminate (osThreadGetId()); }
void Th_Thr5 (void *arg) { Var_ThreadExec += (arg == NULL) ? (1) : (2); osThreadTerminate (osThreadGetId()); }
void Th_Thr6 (void *arg) { Var_ThreadExec += (arg == NULL) ? (1) : (2); osThreadTerminate (osThreadGetId()); }

/* Th_Run definitions used by multiple test cases */
__NO_RETURN void Th_Run (void __attribute__((unused)) *arg);

static osThreadId_t ExecArr[7];

typedef struct {
  uint32_t  *Cnt;                       /* Counter value                      */
  uint32_t  Res[2];                     /* Result                             */
} YIELD_TEST;

void Th_osThreadGetId_1     (void *arg);
void Th_osThreadGetState_2  (void *arg);
void Th_osThreadGetState_3  (void *arg);
void Th_osThreadSuspend_1   (void *arg);
void Th_osThreadResume_1    (void *arg);
void Th_osThreadResume_2    (void *arg);
void Th_osThreadExit_1      (void *arg) __NO_RETURN;
void Th_osThreadTerminate_1 (void *arg);
void Th_osThreadGetCount_1  (void *arg);
void Th_osThreadEnumerate_1 (void *arg);

void Th_ThreadReturn        (void *arg);
void Th_ThreadMultiInstance (void *arg);
void Th_ThreadPriorityExec  (void *arg);
void Th_YieldTest           (void *arg);
void Th_SuspendResume       (void *arg);
void Th_SelfTerminate       (void *arg);
void Th_Arg                 (void *arg);
void Th_Delay               (void *arg);
void Th_Run                 (void *arg);
void Th_JoinDetach          (void *arg);

void Irq_osThreadNew_1           (void);
void Irq_osThreadGetName_1       (void);
void Irq_osThreadGetId_1         (void);
void Irq_osThreadGetState_1      (void);
void Irq_osThreadSetPriority_2   (void);
void Irq_osThreadGetPriority_1   (void);
void Irq_osThreadYield_1         (void);
void Irq_osThreadSuspend_1       (void);
void Irq_osThreadResume_1        (void);
void Irq_osThreadDetach_2        (void);
void Irq_osThreadJoin_2          (void);
void Irq_osThreadTerminate_1     (void);
void Irq_osThreadGetStackSize_1  (void);
void Irq_osThreadGetStackSpace_1 (void);
void Irq_osThreadGetCount_1      (void);
void Irq_osThreadEnumerate_1     (void);

/*-----------------------------------------------------------------------------
 * Counting thread
 *----------------------------------------------------------------------------*/
__NO_RETURN void Th_CountingThread  (void __attribute__((unused)) *arg) {
  while(1) {
    Var_Counter++;
    osDelay (5);
  }
}

/*-----------------------------------------------------------------------------
 * Test thread for TC_ThreadJoinDetach
 *----------------------------------------------------------------------------*/
void Th_JoinDetach (void *arg) {
  int32_t *cnt = (int32_t *)arg;
  osDelay(10);
  (*cnt)++;

  /* Explicitly terminate this thread */
  osThreadTerminate (osThreadGetId());
}

/*-----------------------------------------------------------------------------
 * Thread that terminates itself
 *----------------------------------------------------------------------------*/
void Th_SelfTerminate (void *arg) {
  (void)arg;

  osThreadTerminate (osThreadGetId());
}

/*-----------------------------------------------------------------------------
 * Thread that delays itself forever
 *----------------------------------------------------------------------------*/
void Th_Delay (void *arg) {
  (void)arg;

  osDelay (osWaitForever);
}

/*-----------------------------------------------------------------------------
 * Thread that runs endlessly and yields whenever is executed
 *----------------------------------------------------------------------------*/
void Th_Run (void *arg) {
  (void)arg;

  while(1) {
    osThreadYield();
  }
}

/*-----------------------------------------------------------------------------
 *      Test cases
 *----------------------------------------------------------------------------*/

/*=======0=========1=========2=========3=========4=========5=========6=========7=========8=========9=========0=========1====*/
/**
\defgroup thread_funcs Thread Functions
\brief Thread Functions Test Cases
\details
The test cases check the osThread* functions.

@{
*/

/*=======0=========1=========2=========3=========4=========5=========6=========7=========8=========9=========0=========1====*/
/**
\brief Test case: TC_osThreadNew_1
\details
  - Call osThreadNew to create a thread
  - Call osThreadNew with null thread function
  - Call osThreadNew from ISR
*/
void TC_osThreadNew_1 (void) {
#if (TC_OSTHREADNEW_1_EN)
  osThreadId_t id;

  /* Call osThreadNew to create a thread */
  id = osThreadNew (Th_Run, NULL, NULL);
  ASSERT_TRUE(id != NULL);

  /* Terminate created thread */
  osThreadTerminate (id);

  /* Call osThreadNew with null thread function */
  ASSERT_TRUE (osThreadNew (NULL, NULL, NULL) == NULL);

  /* Call osThreadNew from ISR */
  TST_IRQHandler = Irq_osThreadNew_1;
  ThreadId = (osThreadId_t)(-1);
  SetPendingIRQ(IRQ_A);
  ASSERT_TRUE (ThreadId == NULL);
#endif
}

/*-----------------------------------------------------------------------------
 * TC_osThreadNew_1: ISR handler
 *----------------------------------------------------------------------------*/
#if (TC_OSTHREADNEW_1_EN)
void Irq_osThreadNew_1 (void) {
  ThreadId = osThreadNew (Th_Run, NULL, NULL);
}
#endif

/*=======0=========1=========2=========3=========4=========5=========6=========7=========8=========9=========0=========1====*/
/**
\brief Test case: TC_osThreadNew_2
\details
  - Call osThreadNew and use attributes to create detached thread
*/
void TC_osThreadNew_2 (void) {
#if (TC_OSTHREADNEW_2_EN)
  osThreadAttr_t attr = {NULL, osThreadDetached, NULL, 0U, NULL, 0U, osPriorityNormal, 0U, 0U};
  osThreadId_t tid;

  /* Call osThreadNew and use attributes to create detached thread */
  tid = osThreadNew (Th_Run, NULL, &attr);

  /* Verify that thread was successfully created */
  ASSERT_TRUE(tid != NULL);

  /* Terminate thread */
  ASSERT_TRUE (osThreadTerminate (tid) == osOK);
#endif
}

/*=======0=========1=========2=========3=========4=========5=========6=========7=========8=========9=========0=========1====*/
/**
\brief Test case: TC_osThreadNew_3
\details
  - Call osThreadNew and use attributes to create joinable thread
*/
void TC_osThreadNew_3 (void) {
#if (TC_OSTHREADNEW_3_EN)
  osThreadAttr_t attr = {NULL, osThreadJoinable, NULL, 0U, NULL, 0U, osPriorityNormal, 0U, 0U};
  osThreadId_t tid;

  /* Call osThreadNew and use attributes to create joinable thread */
  tid = osThreadNew (Th_Run, NULL, &attr);

  /* Verify that thread was successfully created */
  ASSERT_TRUE(tid != NULL);

  /* Detach the thread */
  ASSERT_TRUE (osThreadDetach(tid) == osOK);

  /* Terminate thread */
  ASSERT_TRUE (osThreadTerminate (tid) == osOK);
#endif
}

/*=======0=========1=========2=========3=========4=========5=========6=========7=========8=========9=========0=========1====*/
/**
\brief Test case: TC_osThreadNew_4
\details
  - Call osThreadNew and use attributes to create thread with user specified memory for control block and stack
*/
void TC_osThreadNew_4 (void) {
#if (TC_OSTHREADNEW_4_EN)
  osThreadAttr_t attr = {NULL, osThreadDetached, NULL, 0U, NULL, 0U, osPriorityNormal, 0U, 0U};
  osThreadId_t tid;

  /* Call osThreadNew and use attributes to create thread with user specified memory for control block and stack */
  attr.cb_mem     = &Thread_CbMem;
  attr.cb_size    = sizeof(Thread_CbMem);
  attr.stack_mem  = &Thread_StackMem;
  attr.stack_size = sizeof(Thread_StackMem);

  tid = osThreadNew (Th_Run, NULL, &attr);

  /* Verify that thread was successfully created */
  ASSERT_TRUE(tid != NULL);

  /* Terminate thread */
  ASSERT_TRUE (osThreadTerminate (tid) == osOK);
#endif
}

/*=======0=========1=========2=========3=========4=========5=========6=========7=========8=========9=========0=========1====*/
/**
\brief Test case: TC_osThreadNew_5
\details
  - Call osThreadNew and use attributes to create thread with user specified stack size
*/
void TC_osThreadNew_5 (void) {
#if (TC_OSTHREADNEW_5_EN)
  osThreadAttr_t attr = {NULL, osThreadDetached, NULL, 0U, NULL, 0U, osPriorityNormal, 0U, 0U};
  osThreadId_t tid;

  /* Call osThreadNew and use attributes to create thread with user specified stack size */
  attr.stack_size = sizeof(Thread_StackMem);

  tid = osThreadNew (Th_Run, NULL, &attr);

  /* Verify that thread was successfully created */
  ASSERT_TRUE(tid != NULL);

  /* Terminate thread */
  ASSERT_TRUE (osThreadTerminate (tid) == osOK);
#endif
}

/*=======0=========1=========2=========3=========4=========5=========6=========7=========8=========9=========0=========1====*/
/**
\brief Test case: TC_osThreadNew_6
\details
  - Call osThreadNew and use attributes to create thread with user specified priority
*/
void TC_osThreadNew_6 (void) {
#if (TC_OSTHREADNEW_6_EN)
  osThreadAttr_t attr = {NULL, osThreadDetached, NULL, 0U, NULL, 0U, osPriorityNormal, 0U, 0U};
  osThreadId_t tid;
  osPriority_t prio;

  /* Call osThreadNew and use attributes to create thread with user specified priority */
  for (prio = osPriorityLow; prio < osPriorityISR; prio++) {
    /* Set priority */
    attr.priority = prio;

    tid = osThreadNew (Th_Delay, NULL, &attr);

    /* Verify that thread was successfully created */
    ASSERT_TRUE(tid != NULL);

    /* Terminate thread */
    ASSERT_TRUE (osThreadTerminate (tid) == osOK);
  }
#endif
}

/*=======0=========1=========2=========3=========4=========5=========6=========7=========8=========9=========0=========1====*/
/**
\brief Test case: TC_osThreadNew_7
\details
  - Call osThreadNew to create a thread and pass an argument to it
*/
void TC_osThreadNew_7 (void) {
#if (TC_OSTHREADNEW_7_EN)
  osThreadId_t id;
  void *arg;

  /* Call osThreadNew to create a thread and pass an argument to it */
  ThreadArg = NULL;
  arg = ThreadId;

  id = osThreadNew (Th_Arg, arg, NULL);
  ASSERT_TRUE(id != NULL);

  /* Ensure that the created thread executed */
  osDelay(2U);

  /* Verify that the argument was successfully passed */
  ASSERT_TRUE (ThreadArg == arg);
#endif
}

/*-----------------------------------------------------------------------------
 * TC_osThreadNew_7: Helper thread
 *----------------------------------------------------------------------------*/
#if (TC_OSTHREADNEW_7_EN)
void Th_Arg (void *arg) {

  ThreadArg = arg;

  osThreadTerminate (osThreadGetId());
}
#endif

/*=======0=========1=========2=========3=========4=========5=========6=========7=========8=========9=========0=========1====*/
/**
\brief Test case: TC_osThreadGetName_1
\details
  - Call osThreadGetName to retrieve a name of an unnamed thread
  - Call osThreadGetName to retrieve a name of a thread with assigned name
  - Call osThreadGetName from ISR
  - Call osThreadGetName with null object
*/
void TC_osThreadGetName_1 (void) {
#if (TC_OSTHREADGETNAME_1_EN)
  osThreadAttr_t attr = {NULL, 0U, NULL, 0U, NULL, 0U, osPriorityLow, 0U, 0U};
  osThreadId_t id;
  char const *name = "Thread";

  /* Create thread object without assigned name */
  attr.name = NULL;
  id = osThreadNew (Th_SelfTerminate, NULL, &attr);
  ASSERT_TRUE (id != NULL);

  /* Call osThreadGetName to retrieve a name of an unnamed thread */
  ASSERT_TRUE(osThreadGetName (id) == NULL);

  /* Delete thread object */
  osThreadTerminate (id);


  /* Create thread object with name assigned via attributes */
  attr.name = name;
  id = osThreadNew (Th_SelfTerminate, NULL, &attr);
  ASSERT_TRUE (id != NULL);

  /* Call osThreadGetName to retrieve a name of a thread with assigned name */
  ASSERT_TRUE (strcmp(osThreadGetName(id), name) == 0U);

  /* Call osThreadGetName from ISR */
  TST_IRQHandler = Irq_osThreadGetName_1;
  ThreadId   = id;
  ThreadName = name;
  SetPendingIRQ(IRQ_A);
  ASSERT_TRUE (strcmp(ThreadName, name) == 0U);

  /* Delete thread object */
  osThreadTerminate (id);

  /* Call osThreadGetName with null object */
  ASSERT_TRUE (osThreadGetName (NULL) == NULL);
#endif
}

/*-----------------------------------------------------------------------------
 * TC_osThreadGetName_1: ISR handler
 *----------------------------------------------------------------------------*/
#if (TC_OSTHREADGETNAME_1_EN)
void Irq_osThreadGetName_1 (void) {
  ThreadName = osThreadGetName (ThreadId);
}
#endif

/*=======0=========1=========2=========3=========4=========5=========6=========7=========8=========9=========0=========1====*/
/**
\brief Test case: TC_osThreadGetId_1
\details
  - Call osThreadGetId from multiple threads that exist at the same time
  - Call osThreadGetId from ISR
*/
void TC_osThreadGetId_1 (void) {
#if (TC_OSTHREADGETID_1_EN)
  osThreadAttr_t attr = { NULL, osThreadDetached, NULL, 0U, NULL, 0U, osPriorityBelowNormal, 0U, 0U};
  osThreadId_t thread_id[2][MIN_THREAD_NUM];
  osThreadId_t id;
  uint32_t i;

  /* Create multiple threads */
  for (i = 0U; i < MIN_THREAD_NUM; i++) {
    id = osThreadNew (Th_osThreadGetId_1, &thread_id[1][i], &attr);
    ASSERT_TRUE (id != NULL);

    thread_id[0][i] = id;
  }

  /* Allow existing threads to execute */
  osDelay(2U * MIN_THREAD_NUM);

  /* Call osThreadGetId from multiple threads that exist at the same time */
  /* See Th_osThreadGetId_1 */

  /* Check if each thread returned correct ID */
  for (i = 0U; i < MIN_THREAD_NUM; i++) {
    ASSERT_TRUE (thread_id[0][i] == thread_id[1][i]);
  }

  /* Call osThreadGetId from ISR */
  TST_IRQHandler = Irq_osThreadGetId_1;
  Isr_osThreadId = (osThreadId_t)(-1);
  SetPendingIRQ(IRQ_A);
  ASSERT_TRUE (Isr_osThreadId == osThreadGetId());
#endif
}

/*-----------------------------------------------------------------------------
 * TC_osThreadGetId_1: Helper thread
 *----------------------------------------------------------------------------*/
#if (TC_OSTHREADGETID_1_EN)
void Th_osThreadGetId_1 (void *arg) {
  osThreadId_t *p = (osThreadId_t *)arg;

  /* Retrieve own thread id and store it into memory location provided by arg */
  *p = osThreadGetId();

  osThreadTerminate (osThreadGetId());
}
#endif

/*-----------------------------------------------------------------------------
 * TC_osThreadGetId_1: ISR handler
 *----------------------------------------------------------------------------*/
#if (TC_OSTHREADGETID_1_EN)
void Irq_osThreadGetId_1 (void) {
  Isr_osThreadId = osThreadGetId();
}
#endif

/*=======0=========1=========2=========3=========4=========5=========6=========7=========8=========9=========0=========1====*/
/**
\brief Test case: TC_osThreadGetState_1
\details
  - Call osThreadGetState to retrieve the state of a running thread
  - Call osThreadGetState to retrieve the state of a ready thread
  - Call osThreadGetState from ISR
  - Call osThreadGetState to retrieve the state of a terminated thread
  - Call osThreadGetState with null object
*/
void TC_osThreadGetState_1 (void) {
#if (TC_OSTHREADGETSTATE_1_EN)
  osThreadAttr_t attr = { NULL, osThreadDetached, NULL, 0U, NULL, 0U, osPriorityNormal, 0U, 0U};
  osThreadId_t id;
  uint32_t cnt = 0;

  /* Call osThreadGetState to retrieve the state of a running thread */
  ASSERT_TRUE (osThreadGetState(osThreadGetId()) == osThreadRunning);

  /* Synchronize tick */
  osDelay(1U);

  /* Create a thread with the same priority as running thread */
  id = osThreadNew (Th_SelfTerminate, &cnt, &attr);
  ASSERT_TRUE(id != NULL);

  /* Call osThreadGetState to retrieve the state of a ready thread */
  ASSERT_TRUE (osThreadGetState(id) == osThreadReady);

  /* Call osThreadGetState from ISR */
  TST_IRQHandler = Irq_osThreadGetState_1;
  Isr_osThreadState = osThreadRunning;
  ThreadId = id;
  SetPendingIRQ(IRQ_A);
  ASSERT_TRUE (Isr_osThreadState == osThreadError);
  /* Terminate thread */
  ASSERT_TRUE (osThreadTerminate (id) == osOK);

  /* Synchronize tick */
  osDelay(2U);

  /* Call osThreadGetState to retrieve the state of a terminated thread */
  ASSERT_TRUE (osThreadGetState(id) == osThreadError);

  /* Call osThreadGetStackSpace with null object */
  ASSERT_TRUE (osThreadGetState(NULL) == osThreadError);

#endif
}

/*-----------------------------------------------------------------------------
 * TC_osThreadGetState_1: ISR handler
 *----------------------------------------------------------------------------*/
#if (TC_OSTHREADGETSTATE_1_EN)
void Irq_osThreadGetState_1 (void) {
  Isr_osThreadState = osThreadGetState(ThreadId);
}
#endif

/*=======0=========1=========2=========3=========4=========5=========6=========7=========8=========9=========0=========1====*/
/**
\brief Test case: TC_osThreadGetState_2
\details
  - Call osThreadGetState to retrieve the state of a blocked thread
*/
void TC_osThreadGetState_2 (void) {
#if (TC_OSTHREADGETSTATE_2_EN)
  osThreadAttr_t attr = { NULL, osThreadDetached, NULL, 0U, NULL, 0U, osPriorityHigh, 0U, 0U};
  osThreadId_t id;

  /* Create a semaphore object */
  SemaphoreId = osSemaphoreNew (1U, 0U, NULL);
  ASSERT_TRUE(SemaphoreId != NULL);

  /* Create a thread that tries to acquire a semaphore that is not available */
  id = osThreadNew (Th_osThreadGetState_2, NULL, &attr);
  ASSERT_TRUE(id != NULL);

  /* Call osThreadGetState to retrieve the state of a blocked thread */
  ASSERT_TRUE (osThreadGetState(id) == osThreadBlocked);

  /* Terminate thread and delete semaphore */
  ASSERT_TRUE (osThreadTerminate (id) == osOK);
  ASSERT_TRUE (osSemaphoreDelete (SemaphoreId) == osOK);
#endif
}

/*-----------------------------------------------------------------------------
 * TC_osThreadGetState_2: Helper thread
 *----------------------------------------------------------------------------*/
#if (TC_OSTHREADGETSTATE_2_EN)
void Th_osThreadGetState_2 (void *arg) {
  (void)arg;

  ASSERT_TRUE (osSemaphoreAcquire (SemaphoreId, osWaitForever) == osOK);

//  osThreadTerminate (osThreadGetId());
}
#endif

/*=======0=========1=========2=========3=========4=========5=========6=========7=========8=========9=========0=========1====*/
/**
\brief Test case: TC_osThreadGetState_3
\details
  - Call osThreadGetState to retrieve the state of a terminated joinable thread
*/
void TC_osThreadGetState_3 (void) {
#if (TC_OSTHREADGETSTATE_3_EN)
  osThreadAttr_t attr = { NULL, 0U, NULL, 0U, NULL, 0U, osPriorityBelowNormal, 0U, 0U };
  osThreadId_t id;

  /* Create a joinable child thread */
  attr.attr_bits = osThreadJoinable;

  id = osThreadNew (Th_osThreadGetState_3, NULL, &attr);
  ASSERT_TRUE (id != NULL);

  /* Terminate the thread */
  ASSERT_TRUE (osThreadTerminate (id) == osOK);

  /* Check the thread is terminated */
  ASSERT_TRUE ((osThreadGetState (id) == osThreadTerminated));

  /* Detach the terminated threads to release resources */
  ASSERT_TRUE (osThreadDetach(id) == osOK);
#endif
}

/*-----------------------------------------------------------------------------
 * TC_osThreadGetState_3: Helper thread
 *----------------------------------------------------------------------------*/
#if (TC_OSTHREADGETSTATE_3_EN)
void Th_osThreadGetState_3 (void *arg) {
  (void)arg;

  osThreadTerminate (osThreadGetId());
}
#endif

/*=======0=========1=========2=========3=========4=========5=========6=========7=========8=========9=========0=========1====*/
/**
\brief Test case: TC_osThreadSetPriority_1
\details
  - Call osThreadSetPriority to change priority of a running thread in steps from Low to Realtime
  - Call osThreadSetPriority to change priority of a child thread in steps from Low to Realtime
*/
void TC_osThreadSetPriority_1 (void) {
#if (TC_OSTHREADSETPRIORITY_1_EN)
  osThreadAttr_t attr = { NULL, osThreadDetached, NULL, 0U, NULL, 0U, osPriorityLow, 0U, 0U};

  /* Get main thread ID */
  ThreadId = osThreadGetId();
  ASSERT_TRUE (ThreadId != NULL);
  /* Call osThreadSetPriority to change priority of a running thread in steps from Low to Realtime */
  ASSERT_TRUE (osThreadSetPriority (ThreadId, osPriorityLow) == osOK);
  ASSERT_TRUE (osThreadGetPriority (ThreadId) == osPriorityLow);

  ASSERT_TRUE (osThreadSetPriority (ThreadId, osPriorityBelowNormal) == osOK);
  ASSERT_TRUE (osThreadGetPriority (ThreadId) == osPriorityBelowNormal);

  ASSERT_TRUE (osThreadSetPriority (ThreadId, osPriorityNormal) == osOK);
  ASSERT_TRUE (osThreadGetPriority (ThreadId) == osPriorityNormal);

  ASSERT_TRUE (osThreadSetPriority (ThreadId, osPriorityAboveNormal) == osOK);
  ASSERT_TRUE (osThreadGetPriority (ThreadId) == osPriorityAboveNormal);

  ASSERT_TRUE (osThreadSetPriority (ThreadId, osPriorityHigh) == osOK);
  ASSERT_TRUE (osThreadGetPriority (ThreadId) == osPriorityHigh);

  ASSERT_TRUE (osThreadSetPriority (ThreadId, osPriorityRealtime) == osOK);
  ASSERT_TRUE (osThreadGetPriority (ThreadId) == osPriorityRealtime);

  /* Create a child thread */
  ThreadId = osThreadNew (Th_Run, NULL, &attr);
  ASSERT_TRUE (ThreadId != NULL);

  /* Call osThreadSetPriority to change priority of a child thread in steps from Low to Realtime */
  ASSERT_TRUE (osThreadSetPriority (ThreadId, osPriorityLow) == osOK);
  ASSERT_TRUE (osThreadGetPriority (ThreadId) == osPriorityLow);

  ASSERT_TRUE (osThreadSetPriority (ThreadId, osPriorityBelowNormal) == osOK);
  ASSERT_TRUE (osThreadGetPriority (ThreadId) == osPriorityBelowNormal);

  ASSERT_TRUE (osThreadSetPriority (ThreadId, osPriorityNormal) == osOK);
  ASSERT_TRUE (osThreadGetPriority (ThreadId) == osPriorityNormal);

  ASSERT_TRUE (osThreadSetPriority (ThreadId, osPriorityAboveNormal) == osOK);
  ASSERT_TRUE (osThreadGetPriority (ThreadId) == osPriorityAboveNormal);

  ASSERT_TRUE (osThreadSetPriority (ThreadId, osPriorityHigh) == osOK);
  ASSERT_TRUE (osThreadGetPriority (ThreadId) == osPriorityHigh);

  ASSERT_TRUE (osThreadSetPriority (ThreadId, osPriorityRealtime) == osOK);
  ASSERT_TRUE (osThreadGetPriority (ThreadId) == osPriorityRealtime);

  /* Terminate the thread */
  osThreadTerminate (ThreadId);

  /* Restore priority of the main thread back to normal */
  osThreadSetPriority (osThreadGetId(), osPriorityNormal);
#endif
}

/*=======0=========1=========2=========3=========4=========5=========6=========7=========8=========9=========0=========1====*/
/**
\brief Test case: TC_osThreadSetPriority_2
\details
  - Call osThreadSetPriority with priority lower than osPriorityIdle
  - Call osThreadSetPriority with priority higher than osPriorityISR
  - Call osThreadSetPriority from ISR
  - Call osThreadSetPriority with null object
*/
void TC_osThreadSetPriority_2 (void) {
#if (TC_OSTHREADSETPRIORITY_2_EN)
  osThreadAttr_t attr = { NULL, osThreadDetached, NULL, 0U, NULL, 0U, osPriorityLow, 0U, 0U};
  osThreadId_t id;

  /* Create a child thread */
  id = osThreadNew (Th_SelfTerminate, NULL, &attr);
  ASSERT_TRUE (id != NULL);

  /* Call osThreadSetPriority with priority lower than osPriorityIdle */
  ASSERT_TRUE (osThreadSetPriority (id, (osPriority_t)(osPriorityIdle - 1U)) == osErrorParameter);

  /* Call osThreadSetPriority with priority higher than osPriorityISR */
  ASSERT_TRUE (osThreadSetPriority (id, (osPriority_t)(osPriorityISR + 1U)) == osErrorParameter);

  /* Call osThreadSetPriority from ISR */
  TST_IRQHandler = Irq_osThreadSetPriority_2;
  Isr_osStatus = osOK;
  ThreadId = id;
  SetPendingIRQ(IRQ_A);
  ASSERT_TRUE (Isr_osStatus == osErrorISR);

  /* Terminate thread */
  osThreadTerminate (id);

  /* Call osThreadSetPriority with null object */
  ASSERT_TRUE (osThreadSetPriority(NULL, osPriorityBelowNormal) == osErrorParameter);
#endif
}

/*-----------------------------------------------------------------------------
 * TC_osThreadSetPriority_2: ISR handler
 *----------------------------------------------------------------------------*/
#if (TC_OSTHREADSETPRIORITY_2_EN)
void Irq_osThreadSetPriority_2 (void) {
  Isr_osStatus = osThreadSetPriority(ThreadId, osPriorityHigh);
}
#endif

/*=======0=========1=========2=========3=========4=========5=========6=========7=========8=========9=========0=========1====*/
/**
\brief Test case: TC_osThreadGetPriority_1
\details
  - Call osThreadGetPriority to retrieve priority of a running thread
  - Call osThreadGetPriority from ISR
  - Call osThreadGetPriority with null object
*/
void TC_osThreadGetPriority_1 (void) {
#if (TC_OSTHREADGETPRIORITY_1_EN)
  osThreadId_t id;

  id = osThreadGetId();

  /* Call osThreadGetPriority to retrieve priority of a running thread */
  ASSERT_TRUE (osThreadGetPriority(id) == osPriorityNormal);

  /* Call osThreadGetPriority from ISR */
  TST_IRQHandler = Irq_osThreadGetPriority_1;
  Isr_osPriority = osPriorityNone;
  ThreadId = id;
  SetPendingIRQ(IRQ_A);
  ASSERT_TRUE (Isr_osPriority == osPriorityError);

  /* Call osThreadGetPriority with null object */
  ASSERT_TRUE (osThreadGetPriority(NULL) == osPriorityError);
#endif
}

/*-----------------------------------------------------------------------------
 * TC_osThreadGetPriority_1: ISR handler
 *----------------------------------------------------------------------------*/
#if (TC_OSTHREADGETPRIORITY_1_EN)
void Irq_osThreadGetPriority_1 (void) {
  Isr_osPriority = osThreadGetPriority(ThreadId);
}
#endif

/*=======0=========1=========2=========3=========4=========5=========6=========7=========8=========9=========0=========1====*/
/**
\brief Test case: TC_osThreadYield_1
\details
  - Call osThreadYield with no thread in state 'Ready'
  - Call osThreadYield from ISR
*/
void TC_osThreadYield_1 (void) {
#if (TC_OSTHREADYIELD_1_EN)
  /* Call osThreadYield with no thread in state 'Ready' */
  ASSERT_TRUE(osThreadYield() == osOK);

  /* Call osThreadYield from ISR */
  TST_IRQHandler = Irq_osThreadYield_1;
  Isr_osStatus = osOK;
  SetPendingIRQ(IRQ_A);
  ASSERT_TRUE (Isr_osStatus == osErrorISR);
#endif
}

/*-----------------------------------------------------------------------------
 * TC_osThreadYield_1: ISR handler
 *----------------------------------------------------------------------------*/
#if (TC_OSTHREADYIELD_1_EN)
void Irq_osThreadYield_1 (void) {
  Isr_osStatus = osThreadYield();
}
#endif

/*=======0=========1=========2=========3=========4=========5=========6=========7=========8=========9=========0=========1====*/
/**
\brief Test case: TC_osThreadSuspend_1
\details
  - Call osThreadSuspend to suspend a thread when there is at least one other thread 'Ready'
  - Call osThreadSuspend to suspend a child thread which is in 'Ready' state
  - Call osThreadSuspend from ISR
  - Call osThreadSuspend with null object
*/
void TC_osThreadSuspend_1 (void) {
#if (TC_OSTHREADSUSPEND_1_EN)
  osThreadAttr_t attr = { NULL, osThreadDetached, NULL, 0U, NULL, 0U, osPriorityHigh, 0U, 0U};
  osThreadId_t id;
  uint32_t cnt;

  /* Create a thread */
  cnt = 0U;
  id = osThreadNew (Th_osThreadSuspend_1, &cnt, &attr);
  ASSERT_TRUE(id != NULL);

  /* Verify that the thread was suspended */
  ASSERT_TRUE (cnt == 1U);

  /* Terminate created thread */
  osThreadTerminate (id);


  /* Create a thread */
  attr.priority = osPriorityLow;
  cnt = 0U;
  id = osThreadNew (Th_osThreadSuspend_1, &cnt, &attr);
  ASSERT_TRUE(id != NULL);

  /* Check that the thread is in ready state */
  ASSERT_TRUE (osThreadGetState (id) == osThreadReady);

  /* Call osThreadSuspend to suspend a child thread */
  ASSERT_TRUE (osThreadSuspend(id) == osOK);

  /* Check that the thread is in blocked state */
  ASSERT_TRUE (osThreadGetState (id) == osThreadBlocked);

  /* Terminate created thread */
  osThreadTerminate (id);


  /* Create a thread */
  attr.priority = osPriorityLow;
  cnt = 0U;
  id = osThreadNew (Th_osThreadSuspend_1, &cnt, &attr);
  ASSERT_TRUE(id != NULL);

  /* Call osThreadSuspend from ISR */
  TST_IRQHandler = Irq_osThreadSuspend_1;
  Isr_osStatus = osOK;
  SetPendingIRQ(IRQ_A);
  ASSERT_TRUE (Isr_osStatus == osErrorISR);

  /* Terminate thread */
  osThreadTerminate (id);

  /* Call osThreadSuspend with null object */
  ASSERT_TRUE (osThreadSuspend(NULL) == osErrorParameter);

#endif
}

/*-----------------------------------------------------------------------------
 * TC_osThreadSuspend_1: Helper thread
 *----------------------------------------------------------------------------*/
#if (TC_OSTHREADSUSPEND_1_EN)
void Th_osThreadSuspend_1 (void *arg) {
  uint32_t *cnt = (uint32_t *)arg;
  osThreadId_t id = osThreadGetId();

  /* Increment counter (indicate that the thread has been started */
  (*cnt)++;

  /* Call osThreadSuspend to suspend a thread when there is at least one other thread 'Ready' */
  ASSERT_TRUE(osThreadSuspend(id) == osOK);

  /* Increment counter (indicate that osThreadSuspend didn't work */
  (*cnt)++;

  /* Terminate this thread (safety) */
  osThreadTerminate (id);
}
#endif

/*-----------------------------------------------------------------------------
 * TC_osThreadSuspend_1: ISR handler
 *----------------------------------------------------------------------------*/
#if (TC_OSTHREADSUSPEND_1_EN)
void Irq_osThreadSuspend_1 (void) {
  Isr_osStatus = osThreadSuspend(ThreadId);
}
#endif

/*=======0=========1=========2=========3=========4=========5=========6=========7=========8=========9=========0=========1====*/
/**
\brief Test case: TC_osThreadResume_1
\details
  - Call osThreadResume to resume suspended thread
  - Call osThreadResume from ISR
  - Call osThreadResume with null object
*/
void TC_osThreadResume_1 (void) {
#if (TC_OSTHREADRESUME_1_EN)
  osThreadAttr_t attr = { NULL, osThreadDetached, NULL, 0U, NULL, 0U, osPriorityHigh, 0U, 0U};
  osThreadId_t id;
  uint32_t cnt;

  /* Create a thread */
  cnt = 0U;
  id = osThreadNew (Th_osThreadResume_1, &cnt, &attr);
  ASSERT_TRUE(id != NULL);

  /* Check that the thread is in blocked state */
  ASSERT_TRUE (osThreadGetState (id) == osThreadBlocked);

  /* Call osThreadResume to resume suspended thread */
  ASSERT_TRUE (osThreadResume (id) == osOK);

  /* Check that the thread was resumed */
  ASSERT_TRUE (cnt == 2U);

  /* Terminate created thread */
  osThreadTerminate (id);


  /* Create a thread */
  attr.priority = osPriorityLow;
  cnt = 0U;
  id = osThreadNew (Th_osThreadResume_1, &cnt, &attr);
  ASSERT_TRUE(id != NULL);

  /* Suspend created thread */
  ASSERT_TRUE (osThreadSuspend(id) == osOK);

  /* Call osThreadResume from ISR */
  TST_IRQHandler = Irq_osThreadResume_1;
  Isr_osStatus = osOK;
  SetPendingIRQ(IRQ_A);
  ASSERT_TRUE (Isr_osStatus == osErrorISR);

  /* Terminate thread */
  osThreadTerminate (id);

  /* Call osThreadResume with null object */
  ASSERT_TRUE (osThreadResume(NULL) == osErrorParameter);
#endif
}

/*-----------------------------------------------------------------------------
 * TC_osThreadResume_1: Helper thread
 *----------------------------------------------------------------------------*/
#if (TC_OSTHREADRESUME_1_EN)
void Th_osThreadResume_1 (void *arg) {
  uint32_t *cnt = (uint32_t *)arg;
  osThreadId_t id = osThreadGetId();

  /* Increment counter (indicate that the thread has been started */
  (*cnt)++;

  /* Call osThreadSuspend to suspend a thread when there is at least one other thread 'Ready' */
  ASSERT_TRUE(osThreadSuspend(id) == osOK);

  /* Increment counter (indicate that the thread was resumed */
  (*cnt)++;

  osDelay(osWaitForever);
}
#endif

/*-----------------------------------------------------------------------------
 * TC_osThreadResume_1: ISR handler
 *----------------------------------------------------------------------------*/
#if (TC_OSTHREADRESUME_1_EN)
void Irq_osThreadResume_1 (void) {
  Isr_osStatus = osThreadResume(ThreadId);
}
#endif

/*=======0=========1=========2=========3=========4=========5=========6=========7=========8=========9=========0=========1====*/
/**
\brief Test case: TC_osThreadResume_2
\details
  - Call osThreadResume to resume delayed thread
  - Call osThreadResume to resume a thread that waits for mutex
  - Call osThreadResume to resume a thread that waits for semaphore
  - Call osThreadResume to resume a thread that waits for event flags
  - Call osThreadResume to resume a thread that waits for message queue
  - Call osThreadResume to resume a thread that waits for memory pool
*/
void TC_osThreadResume_2 (void) {
#if (TC_OSTHREADRESUME_2_EN)
  osThreadAttr_t attr = { NULL, osThreadDetached, NULL, 0U, NULL, 0U, osPriorityHigh, 0U, 0U};
  osThreadId_t id;
  uint32_t ctrl;

  /* Create required objects */
  MutexId        = osMutexNew(NULL);
  SemaphoreId    = osSemaphoreNew(1U, 1U, NULL);
  EventFlagsId   = osEventFlagsNew(NULL);
  MessageQueueId = osMessageQueueNew(1U, 1U, NULL);
  MemoryPoolId   = osMemoryPoolNew(1U, 1U, NULL);

  /* Create initial conditions */
  ASSERT_TRUE (osMutexAcquire (MutexId, 0U)         == osOK);
  ASSERT_TRUE (osSemaphoreAcquire (SemaphoreId, 0U) == osOK);
  ASSERT_TRUE (osEventFlagsClear (EventFlagsId, 1U) == osOK);
  ASSERT_TRUE (osMessageQueueReset (MessageQueueId) == osOK);
  ASSERT_TRUE (osMemoryPoolAlloc (MemoryPoolId, 0U) != NULL);

  /* Create a thread that is delayed */
  ctrl = 0U;
  id = osThreadNew (Th_osThreadResume_2, &ctrl, &attr);
  ASSERT_TRUE(id != NULL);

  /* Check that the thread is in blocked state */
  ASSERT_TRUE (osThreadGetState (id) == osThreadBlocked);

  /* Call osThreadResume to resume delayed thread */
  ASSERT_TRUE (osThreadResume (id) == osOK);

  /* Check that the thread was resumed */
  ASSERT_TRUE (ctrl == 0xFFU);

  /* Terminate created thread */
  osThreadTerminate (id);


  /* Create a thread that waits for mutex */
  ctrl = 1U;
  id = osThreadNew (Th_osThreadResume_2, &ctrl, &attr);
  ASSERT_TRUE(id != NULL);

  /* Check that the thread is in blocked state */
  ASSERT_TRUE (osThreadGetState (id) == osThreadBlocked);

  /* Call osThreadResume to resume a thread that waits for mutex */
  ASSERT_TRUE (osThreadResume (id) == osOK);

  /* Add delay for potential thread execution after priority inversion */
  osDelay(2U);

  /* Check that the thread was resumed */
  ASSERT_TRUE (ctrl == 0xFFU);

  /* Terminate created thread */
  osThreadTerminate (id);


  /* Create a thread that waits for semaphore */
  ctrl = 2U;
  id = osThreadNew (Th_osThreadResume_2, &ctrl, &attr);
  ASSERT_TRUE(id != NULL);

  /* Check that the thread is in blocked state */
  ASSERT_TRUE (osThreadGetState (id) == osThreadBlocked);

  /* Call osThreadResume to resume a thread that waits for semaphore */
  ASSERT_TRUE (osThreadResume (id) == osOK);

  /* Check that the thread was resumed */
  ASSERT_TRUE (ctrl == 0xFFU);

  /* Terminate created thread */
  osThreadTerminate (id);


  /* Create a thread that waits for event flags */
  ctrl = 3U;
  id = osThreadNew (Th_osThreadResume_2, &ctrl, &attr);
  ASSERT_TRUE(id != NULL);

  /* Check that the thread is in blocked state */
  ASSERT_TRUE (osThreadGetState (id) == osThreadBlocked);

  /* Call osThreadResume to resume a thread that waits for event flags */
  ASSERT_TRUE (osThreadResume (id) == osOK);

  /* Check that the thread was resumed */
  ASSERT_TRUE (ctrl == 0xFFU);

  /* Terminate created thread */
  osThreadTerminate (id);


  /* Create a thread that waits for message queue */
  ctrl = 4U;
  id = osThreadNew (Th_osThreadResume_2, &ctrl, &attr);
  ASSERT_TRUE(id != NULL);

  /* Check that the thread is in blocked state */
  ASSERT_TRUE (osThreadGetState (id) == osThreadBlocked);

  /* Call osThreadResume to resume a thread that waits for message queue */
  ASSERT_TRUE (osThreadResume (id) == osOK);

  /* Check that the thread was resumed */
  ASSERT_TRUE (ctrl == 0xFFU);

  /* Terminate created thread */
  osThreadTerminate (id);


  /* Create a thread that waits for memory pool */
  ctrl = 5U;
  id = osThreadNew (Th_osThreadResume_2, &ctrl, &attr);
  ASSERT_TRUE(id != NULL);

  /* Check that the thread is in blocked state */
  ASSERT_TRUE (osThreadGetState (id) == osThreadBlocked);

  /* Call osThreadResume to resume a thread that waits for memory pool */
  ASSERT_TRUE (osThreadResume (id) == osOK);

  /* Check that the thread was resumed */
  ASSERT_TRUE (ctrl == 0xFFU);

  /* Terminate created thread */
  osThreadTerminate (id);

  /* Delete created objects */
  ASSERT_TRUE (osMutexDelete(MutexId)               == osOK);
  ASSERT_TRUE (osSemaphoreDelete(SemaphoreId)       == osOK);
  ASSERT_TRUE (osEventFlagsDelete(EventFlagsId)     == osOK);
  ASSERT_TRUE (osMessageQueueDelete(MessageQueueId) == osOK);
  ASSERT_TRUE (osMemoryPoolDelete(MemoryPoolId)     == osOK);
#endif
}

/*-----------------------------------------------------------------------------
 * TC_osThreadResume_2: Helper thread
 *----------------------------------------------------------------------------*/
#if (TC_OSTHREADRESUME_2_EN)
void Th_osThreadResume_2 (void *arg) {
  uint32_t *ctrl = (uint32_t *)arg;
  uint8_t msg;

  if (*ctrl == 0U) {
    /* Delay a thread */
    ASSERT_TRUE(osDelay(osWaitForever) == osOK);
  }
  else if (*ctrl == 1U) {
    /* Wait for a mutex without a timeout */
    ASSERT_TRUE(osMutexAcquire(MutexId, osWaitForever) == osErrorTimeout);
  }
  else if (*ctrl == 2U) {
    /* Wait for a semaphore without a timeout */
    ASSERT_TRUE(osSemaphoreAcquire(SemaphoreId, osWaitForever) == osErrorTimeout);
  }
  else if (*ctrl == 3U) {
    /* Wait for event flags without a timeout */
    ASSERT_TRUE(osEventFlagsWait(EventFlagsId, 1U, osFlagsWaitAll, osWaitForever) == osFlagsErrorTimeout);
  }
  else if (*ctrl == 4U) {
    /* Wait for message queue without a timeout */
    ASSERT_TRUE (osMessageQueueGet(MessageQueueId, &msg, NULL, osWaitForever) == osErrorTimeout);
  }
  else if (*ctrl == 5U) {
    /* Wait for memory pool queue without a timeout */
    ASSERT_TRUE (osMemoryPoolAlloc(MemoryPoolId, osWaitForever) == NULL);
  }

  /* Indicate that the thread was resumed */
  *ctrl = 0xFFU;

  osDelay(osWaitForever);
}
#endif

/*=======0=========1=========2=========3=========4=========5=========6=========7=========8=========9=========0=========1====*/
/**
\brief TC_osThreadDetach_1
\details
  - Call osThreadDetach
  - Call osThreadJoin
  - Create a joinable thread and terminate it
  - Verify that thread was terminated
  - Call osThreadDetach with terminated object and verify that thread was invalidated
*/
void TC_osThreadDetach_1 (void) {
#if (TC_OSTHREADDETACH_1_EN)
  osThreadAttr_t attr = { NULL, osThreadJoinable, NULL, 0U, NULL, 0U, osPriorityBelowNormal, 0U, 0U };

  /* Create a joinable thread */
  ThreadId = osThreadNew (Th_JoinDetach, NULL, &attr);
  ASSERT_TRUE (ThreadId != NULL);

  /* Detach the thread */
  ASSERT_TRUE (osThreadDetach (ThreadId) == osOK);

  /* Try to join the thread */
  ASSERT_TRUE (osThreadJoin (ThreadId) == osErrorResource);

  /* Terminate */
  osThreadTerminate (ThreadId);

  /* Create a joinable thread */
  ThreadId = osThreadNew (Th_JoinDetach, NULL, &attr);
  ASSERT_TRUE (ThreadId != NULL);

  /* Terminate */
  osThreadTerminate (ThreadId);

  /* Verify that thread was terminated */
  ASSERT_TRUE (osThreadGetState(ThreadId) == osThreadTerminated);

  /* Call osThreadDetach with terminated object */
  ASSERT_TRUE (osThreadDetach(ThreadId) == osOK);

  /* Verify that thread was invalidated */
  ASSERT_TRUE (osThreadGetState(ThreadId) == osThreadError);
#endif
}

/*=======0=========1=========2=========3=========4=========5=========6=========7=========8=========9=========0=========1====*/
/**
\brief Test case: TC_osThreadDetach_2
\details
  - Call osThreadDetach with a detached thread
  - Call osThreadDetach from ISR
  - Call osThreadDetach with null object
*/
void TC_osThreadDetach_2 (void) {
#if (TC_OSTHREADDETACH_2_EN)
  osThreadAttr_t attr = { NULL, osThreadDetached, NULL, 0U, NULL, 0U, osPriorityBelowNormal, 0U, 0U };
  osThreadId_t id;

  /* Create a detached thread */
  id = osThreadNew (Th_JoinDetach, NULL, &attr);
  ASSERT_TRUE (id != NULL);

  /* Call osThreadDetach with a detached thread */
  ASSERT_TRUE (osThreadDetach(id) == osErrorResource);

  /* Call osThreadDetach from ISR */
  TST_IRQHandler = Irq_osThreadDetach_2;
  ThreadId = id;
  Isr_osStatus = osOK;
  SetPendingIRQ(IRQ_A);
  ASSERT_TRUE (Isr_osStatus == osErrorISR);

  /* Terminate */
  osThreadTerminate (id);

  /* Call osThreadDetach with null object */
  ASSERT_TRUE (osThreadDetach(NULL) == osErrorParameter);
#endif
}

/*-----------------------------------------------------------------------------
 * TC_osThreadDetach_2: ISR handler
 *----------------------------------------------------------------------------*/
#if (TC_OSTHREADDETACH_2_EN)
void Irq_osThreadDetach_2 (void) {
  Isr_osStatus = osThreadDetach(ThreadId);
}
#endif

/*=======0=========1=========2=========3=========4=========5=========6=========7=========8=========9=========0=========1====*/
/**
\brief Test case: TC_osThreadJoin_1
\details
  - Create a low priority joinable thread that terminates itself
  - Call osThreadJoin with the id of the created thread
  - Check that the created thread has terminated
  - Create four threads that are waiting to join each other in a chain
  - Check that all child threads were created and executed
*/
void TC_osThreadJoin_1 (void) {
#if (TC_OSTHREADJOIN_1_EN)
  osThreadAttr_t attr = { NULL, osThreadJoinable, NULL, 0U, NULL, 0U, osPriorityBelowNormal, 0U, 0U };
  osThreadId_t id;
  uint32_t i, arr[4];

  /* Create a joinable thread */
  id = osThreadNew (Th_SelfTerminate, NULL, &attr);
  ASSERT_TRUE(id != NULL);

  /* Verify that thread is in ready state */
  ASSERT_TRUE (osThreadGetState(id) == osThreadReady);

  /* Join the thread */
  ASSERT_TRUE(osThreadJoin(id) == osOK);

  /* Check the thread is inactive */
  ASSERT_TRUE(osThreadGetState(id) == osThreadError);


  /** Create four threads that are waiting to join each other in a chain **/

  /* Clear array */
  for (i = 0U; i < 4U; i++) {
    arr[i] = 0U;
  }

  /* Set thread attributes */
  memset (&ThreadAttr, 0, sizeof(ThreadAttr));

  ThreadAttr.attr_bits = osThreadJoinable;
  ThreadAttr.priority  = osPriorityBelowNormal;

  /* Create a first thread in a chain */
  id = osThreadNew (Th_Child_0, arr, &ThreadAttr);
  ASSERT_TRUE (id != NULL);

  /* Wait until child threads are created and terminated */
  ASSERT_TRUE (osThreadJoin(id) == osOK);

  /* Check that all child threads were created and executed */
  for (i = 0U; i < 4U; i++) {
    ASSERT_TRUE (arr[i] == (i + 1U));
  }
#endif
}

/*-----------------------------------------------------------------------------
 * TC_osThreadJoin_1: Helper threads
 *----------------------------------------------------------------------------*/
#if (TC_OSTHREADJOIN_1_EN)
void Th_Child_0 (void *arg) {
  uint32_t *arr = (uint32_t *)arg;
  osThreadId_t id;

  arr[0] = 1U;

  id = osThreadNew (Th_Child_1, &arr[1], &ThreadAttr);
  ASSERT_TRUE (id != NULL);

  ASSERT_TRUE (osThreadJoin(id) == osOK);

  /* Explicitly terminate this thread */
  osThreadTerminate (osThreadGetId());
}

void Th_Child_1 (void *arg) {
  uint32_t *arr = (uint32_t *)arg;
  osThreadId_t id;

  arr[0] = 2U;

  id = osThreadNew (Th_Child_2, &arr[1], &ThreadAttr);
  ASSERT_TRUE (id != NULL);

  ASSERT_TRUE (osThreadJoin(id) == osOK);

  /* Explicitly terminate this thread */
  osThreadTerminate (osThreadGetId());
}

void Th_Child_2 (void *arg) {
  uint32_t *arr = (uint32_t *)arg;
  osThreadId_t id;

  arr[0] = 3U;

  id = osThreadNew (Th_Child_3, &arr[1], &ThreadAttr);
  ASSERT_TRUE (id != NULL);

  ASSERT_TRUE (osThreadJoin(id) == osOK);

  /* Explicitly terminate this thread */
  osThreadTerminate (osThreadGetId());
}

void Th_Child_3 (void *arg) {
  uint32_t *arr = (uint32_t *)arg;

  arr[0] = 4U;

  /* Explicitly terminate this thread */
  osThreadTerminate (osThreadGetId());
}
#endif

/*=======0=========1=========2=========3=========4=========5=========6=========7=========8=========9=========0=========1====*/
/**
\brief Test case: TC_osThreadJoin_2
\details
  - Call osThreadJoin with null object
  - Call osThreadJoin with a running thread
  - Call osThreadJoin with wrong object id
  - Call osThreadJoin from ISR
  - Call osThreadJoin with a joinable running thread
  - Call osThreadJoin with a joinable terminated thread
*/
void TC_osThreadJoin_2 (void) {
#if (TC_OSTHREADJOIN_2_EN)
  osThreadAttr_t attr = { NULL, osThreadJoinable, NULL, 0U, NULL, 0U, osPriorityBelowNormal, 0U, 0U };
  osThreadId_t tid;
  osMutexId_t mid;

  /* Create a joinable thread */
  tid = osThreadNew (Th_SelfTerminate, NULL, &attr);
  ASSERT_TRUE(tid != NULL);

  /* Call osThreadJoin with null object */
  ASSERT_TRUE (osThreadJoin(NULL) == osErrorParameter);

  /* Call osThreadJoin with a running thread */
  ASSERT_TRUE (osThreadJoin(osThreadGetId()) == osErrorResource);

  /* Call osThreadJoin with wrong object id */
  mid = osMutexNew (NULL);
  ASSERT_TRUE (osThreadJoin(mid) == osErrorParameter);
  osMutexDelete (mid);

  /* Call osThreadJoin from ISR */
  TST_IRQHandler = Irq_osThreadJoin_2;
  ThreadId = tid;
  Isr_osStatus = osOK;
  SetPendingIRQ(IRQ_A);
  ASSERT_TRUE (Isr_osStatus == osErrorISR);

  /* Ensure that Th_SelfTerminate executes */
  osDelay(2U);

  /* Call osThreadJoin with a joinable terminated thread */
  ASSERT_TRUE(osThreadJoin(tid) == osOK);
#endif
}

/*-----------------------------------------------------------------------------
 * TC_osThreadJoin_2: ISR handler
 *----------------------------------------------------------------------------*/
#if (TC_OSTHREADJOIN_2_EN)
void Irq_osThreadJoin_2 (void) {
  Isr_osStatus = osThreadJoin(ThreadId);
}
#endif

/*=======0=========1=========2=========3=========4=========5=========6=========7=========8=========9=========0=========1====*/
/**
\brief Test case: TC_osThreadJoin_3
\details
  - Call osThreadJoin with a detached ready thread
  - Call osThreadJoin with a detached terminated thread (inactive object)
*/
void TC_osThreadJoin_3 (void) {
#if (TC_OSTHREADJOIN_3_EN)
  osThreadAttr_t attr = { NULL, osThreadDetached, NULL, 0U, NULL, 0U, osPriorityBelowNormal, 0U, 0U };
  osThreadId_t tid;

  /* Create a detached thread */
  tid = osThreadNew (Th_SelfTerminate, NULL, &attr);
  ASSERT_TRUE(tid != NULL);

  /* Try to join the detached thread */
  ASSERT_TRUE(osThreadJoin(tid) == osErrorResource);

  /* Terminate thread */
  osThreadTerminate (tid);

  /* Call osThreadJoin with inactive object */
  ASSERT_TRUE(osThreadJoin(ThreadId) == osErrorParameter);
#endif
}

/*=======0=========1=========2=========3=========4=========5=========6=========7=========8=========9=========0=========1====*/
/**
\brief Test case: TC_osThreadExit_1
\details
  - Call osThreadExit to terminate the running thread
*/
void TC_osThreadExit_1 (void) {
#if (TC_OSTHREADEXIT_1_EN)
  osThreadAttr_t attr = { NULL, osThreadDetached, NULL, 0U, NULL, 0U, osPriorityHigh, 0U, 0U };
  osThreadId_t id;
  uint32_t cnt;

  cnt = 0U;

  /* Create a thread */
  id = osThreadNew (Th_osThreadExit_1, &cnt, &attr);
  ASSERT_TRUE(id != NULL);

  /* Check that the thread was started and osThreadExit did not return */
  ASSERT_TRUE (cnt == 1U);

  /* Check that the thread is terminated */
  ASSERT_TRUE (osThreadGetState (id) == osThreadError);
#endif
}

/*-----------------------------------------------------------------------------
 * TC_osThreadExit_1: Helper thread
 *----------------------------------------------------------------------------*/
#if (TC_OSTHREADEXIT_1_EN)
void Th_osThreadExit_1 (void *arg) {
  uint32_t *cnt = (uint32_t *)arg;

  for (;;) {
    /* Increment counter (indicate that the thread has been started or not terminated */
    (*cnt)++;

    /* Call osThreadExit to terminate the running thread */
    osThreadExit();
  }
}
#endif

/*=======0=========1=========2=========3=========4=========5=========6=========7=========8=========9=========0=========1====*/
/**
\brief Test case: TC_osThreadTerminate_1
\details
  - Call osThreadTerminate to terminate thread in state 'Ready'
  - Call osThreadTerminate to terminate thread in state 'Blocked' (delayed)
  - Call osThreadTerminate from ISR
*/
void TC_osThreadTerminate_1 (void) {
#if (TC_OSTHREADTERMINATE_1_EN)
  osThreadAttr_t attr = { NULL, osThreadDetached, NULL, 0U, NULL, 0U, osPriorityNone, 0U, 0U};
  osThreadId_t id;

  /* Create a child thread */
  attr.priority = osPriorityLow;
  id = osThreadNew (Th_osThreadTerminate_1, NULL, &attr);
  ASSERT_TRUE(id != NULL);

  /* Check that the thread is in ready state */
  ASSERT_TRUE (osThreadGetState (id) == osThreadReady);

  /* Call osThreadTerminate to terminate thread in state 'Ready' */
  ASSERT_TRUE (osThreadTerminate(id) == osOK);

  /* Check that the thread state is invalid */
  ASSERT_TRUE (osThreadGetState (id) == osThreadError);


  /* Create a child thread */
  attr.priority = osPriorityHigh;
  id = osThreadNew (Th_osThreadTerminate_1, NULL, &attr);
  ASSERT_TRUE(id != NULL);

  /* Check that the thread is in blocked state */
  ASSERT_TRUE (osThreadGetState (id) == osThreadBlocked);

  /* Call osThreadTerminate to terminate thread in state 'Blocked' (delayed) */
  ASSERT_TRUE (osThreadTerminate(id) == osOK);

  /* Check that the thread state is invalid */
  ASSERT_TRUE (osThreadGetState (id) == osThreadError);


  /* Create a child thread */
  attr.priority = osPriorityLow;
  id = osThreadNew (Th_osThreadTerminate_1, NULL, &attr);
  ASSERT_TRUE(id != NULL);

  /* Call osThreadTerminate from ISR */
  TST_IRQHandler = Irq_osThreadTerminate_1;
  Isr_osStatus = osOK;
  ThreadId = id;
  SetPendingIRQ(IRQ_A);
  ASSERT_TRUE (Isr_osStatus == osErrorISR);

  /* Terminate created thread */
  ASSERT_TRUE (osThreadTerminate(id) == osOK);
#endif
}

/*-----------------------------------------------------------------------------
 * TC_osThreadTerminate_1: Helper thread
 *----------------------------------------------------------------------------*/
#if (TC_OSTHREADTERMINATE_1_EN)
void Th_osThreadTerminate_1 (void *arg) {
  (void)arg;

  osDelay(osWaitForever);
}
#endif

/*-----------------------------------------------------------------------------
 * TC_osThreadTerminate_1: ISR handler
 *----------------------------------------------------------------------------*/
#if (TC_OSTHREADTERMINATE_1_EN)
void Irq_osThreadTerminate_1 (void) {

  Isr_osStatus = osThreadTerminate(ThreadId);
}
#endif

/*=======0=========1=========2=========3=========4=========5=========6=========7=========8=========9=========0=========1====*/
/**
\brief Test case: TC_osThreadGetStackSize_1
\details
  - Call osThreadGetStackSize to retrieve the stack size of a running thread
  - Call osThreadGetStackSize to retrieve the stack size of a 'Ready' thread
  - Call osThreadGetStackSize from ISR
  - Call osThreadGetStackSize with null object id
*/
void TC_osThreadGetStackSize_1 (void) {
#if (TC_OSTHREADGETSTACKSIZE_1_EN)
  osThreadAttr_t attr = {NULL, osThreadDetached, NULL, 0U, NULL, 128U, osPriorityLow, 0U, 0U};
  osThreadId_t id;

  /* Call osThreadGetStackSize to retrieve the stack size of a running thread */
  id = osThreadGetId();
  ASSERT_TRUE(osThreadGetStackSize(id) == MAIN_THREAD_STACK);

  /* Create a thread with a stack size of 128 bytes */
  id = osThreadNew (Th_SelfTerminate, NULL, &attr);
  ASSERT_TRUE(id != NULL);

  /* Call osThreadGetStackSize to retrieve the stack size of a 'Ready' thread */
  ASSERT_TRUE(osThreadGetStackSize(id) == 128U);

  /* Call osThreadGetStackSize from ISR */
  TST_IRQHandler = Irq_osThreadGetStackSize_1;
  Isr_u32 = 128U;
  ThreadId = id;
  SetPendingIRQ(IRQ_A);
  ASSERT_TRUE (Isr_u32 == 0U);

  /* Terminate thread */
  osThreadTerminate (id);

  /* Call osThreadGetStackSize with null object */
  ASSERT_TRUE (osThreadGetStackSize(NULL) == 0U);
#endif
}

/*-----------------------------------------------------------------------------
 * TC_osThreadGetStackSize_1: ISR handler
 *----------------------------------------------------------------------------*/
#if (TC_OSTHREADGETSTACKSIZE_1_EN)
void Irq_osThreadGetStackSize_1 (void) {

  Isr_u32 = osThreadGetStackSize(ThreadId);
}
#endif

/*=======0=========1=========2=========3=========4=========5=========6=========7=========8=========9=========0=========1====*/
/**
\brief Test case: TC_osThreadGetStackSpace_1
\details
  - Call osThreadGetStackSpace to retrieve the unused stack space of a running thread
  - Call osThreadGetStackSpace to retrieve the unused stack space of a ready thread
  - Call osThreadGetStackSpace from ISR
  - Call osThreadGetStackSpace with null object
*/
void TC_osThreadGetStackSpace_1 (void) {
#if (TC_OSTHREADGETSTACKSPACE_1_EN)
  uint32_t size;
  osThreadAttr_t attr = {NULL, osThreadDetached, NULL, 0U, NULL, 128U, osPriorityLow, 0U, 0U};
  osThreadId_t id;

  /* Call osThreadGetStackSpace to retrieve the unused stack space of a running thread */
  id = osThreadGetId();
  size = osThreadGetStackSpace(id);
  ASSERT_TRUE (size > 0U);
  ASSERT_TRUE (size < MAIN_THREAD_STACK);

  /* Create a child thread with 128 bytes stack */
  id = osThreadNew (Th_Run, NULL, &attr);
  ASSERT_TRUE (id != NULL);

  /* Call osThreadGetStackSpace to retrieve the unused stack space of a ready thread */
  size = osThreadGetStackSpace(id);
  ASSERT_TRUE (size < 128U);
  ASSERT_TRUE (size > 0U);

  osThreadTerminate (id);

  /* Call osThreadGetStackSpace from ISR */
  TST_IRQHandler = Irq_osThreadGetStackSpace_1;
  Isr_u32 = 128U;
  ThreadId = id;
  SetPendingIRQ(IRQ_A);
  ASSERT_TRUE (Isr_u32 == 0U);

  /* Terminate thread */
  osThreadTerminate (id);

  /* Call osThreadGetStackSpace with null object */
  ASSERT_TRUE (osThreadGetStackSpace(NULL) == 0U);
#endif
}

/*-----------------------------------------------------------------------------
 * TC_osThreadGetStackSize_1: ISR handler
 *----------------------------------------------------------------------------*/
#if (TC_OSTHREADGETSTACKSPACE_1_EN)
void Irq_osThreadGetStackSpace_1 (void) {

  Isr_u32 = osThreadGetStackSpace(ThreadId);
}
#endif

/*=======0=========1=========2=========3=========4=========5=========6=========7=========8=========9=========0=========1====*/
/**
\brief Test case: TC_osThreadGetCount_1
\details
  - Call osThreadGetCount to retrieve the number of active threads
  - Call osThreadGetCount from ISR
*/
void TC_osThreadGetCount_1 (void) {
#if (TC_OSTHREADGETCOUNT_1_EN)
  osThreadAttr_t attr = { NULL, osThreadDetached, NULL, 0U, NULL, 0U, osPriorityNone, 0U, 0U};
  osThreadId_t id[2];
  uint32_t cnt;

  /* Get initial thread count */
  cnt = osThreadGetCount();
  ASSERT_TRUE (cnt > 0U);

  /* Create a thread that will stay blocked (delayed) */
  attr.priority = osPriorityHigh;
  id[0] = osThreadNew (Th_osThreadGetCount_1, NULL, &attr);
  ASSERT_TRUE(id[0] != NULL);

  /* Create a thread that will stay ready */
  attr.priority = osPriorityLow;
  id[1] = osThreadNew (Th_SelfTerminate, NULL, &attr);
  ASSERT_TRUE(id[1] != NULL);

  /* Call osThreadGetCount to retrieve the number of active threads */
  ASSERT_TRUE (osThreadGetCount() == (cnt + 2U));

  /* Terminate threads */
  osThreadTerminate (id[0]);
  osThreadTerminate (id[1]);

  /* Call osThreadGetCount from ISR */
  TST_IRQHandler = Irq_osThreadGetCount_1;
  Isr_u32 = UINT32_MAX;
  SetPendingIRQ(IRQ_A);
  ASSERT_TRUE (Isr_u32 == 0U);
#endif
}

/*-----------------------------------------------------------------------------
 * TC_osThreadGetCount_1: Helper thread
 *----------------------------------------------------------------------------*/
#if (TC_OSTHREADGETCOUNT_1_EN)
void Th_osThreadGetCount_1 (void *arg) {
  (void)arg;

  osDelay(osWaitForever);
}
#endif

/*-----------------------------------------------------------------------------
 * TC_osThreadGetCount_1: ISR handler
 *----------------------------------------------------------------------------*/
#if (TC_OSTHREADGETCOUNT_1_EN)
void Irq_osThreadGetCount_1 (void) {

  Isr_u32 = osThreadGetCount();
}
#endif

/*=======0=========1=========2=========3=========4=========5=========6=========7=========8=========9=========0=========1====*/
/**
\brief Test case: TC_osThreadEnumerate_1
\details
  - Call osThreadEnumerate to retrieve IDs of all active threads
  - Call osThreadEnumerate from ISR
*/
void TC_osThreadEnumerate_1 (void) {
#if (TC_OSTHREADENUMERATE_1_EN)
  osThreadAttr_t attr = { NULL, osThreadDetached, NULL, 0U, NULL, 0U, osPriorityNone, 0U, 0U};
  osThreadId_t id[2];
  osThreadId_t id_enum[10];
  uint32_t cnt;
  uint32_t i;

  /* Create a thread that will stay blocked (delayed) */
  attr.priority = osPriorityHigh;
  id[0] = osThreadNew (Th_osThreadEnumerate_1, NULL, &attr);
  ASSERT_TRUE(id[0] != NULL);

  /* Create a thread that will stay ready */
  attr.priority = osPriorityLow;
  id[1] = osThreadNew (Th_SelfTerminate, NULL, &attr);
  ASSERT_TRUE(id[1] != NULL);

  /* Call osThreadEnumerate to retrieve IDs of all active threads */
  cnt = osThreadEnumerate(id_enum, 10U);
  ASSERT_TRUE (cnt > 0U);
  ASSERT_TRUE (cnt < 10U);

  /* Check that ID of blocked thread was returned in enum array */
  for (i = 0; i < 10U; i++) {
    if (id_enum[i] == id[0]) {
      break;
    }
  }
  ASSERT_TRUE (i < 10U);

  /* Check that ID of ready thread was returned in enum array */
  for (i = 0; i < 10U; i++) {
    if (id_enum[i] == id[1]) {
      break;
    }
  }
  ASSERT_TRUE (i < 10U);

  /* Terminate threads */
  osThreadTerminate (id[0]);
  osThreadTerminate (id[1]);

  /* Call osThreadEnumerate from ISR */
  TST_IRQHandler = Irq_osThreadEnumerate_1;
  Isr_u32 = UINT32_MAX;
  SetPendingIRQ(IRQ_A);
  ASSERT_TRUE (Isr_u32 == 0U);
#endif
}

/*-----------------------------------------------------------------------------
 * TC_osThreadEnumerate_1: Helper thread
 *----------------------------------------------------------------------------*/
#if (TC_OSTHREADENUMERATE_1_EN)
void Th_osThreadEnumerate_1 (void *arg) {
  (void)arg;

  osDelay(osWaitForever);
}
#endif

/*-----------------------------------------------------------------------------
 * TC_osThreadEnumerate_1: ISR handler
 *----------------------------------------------------------------------------*/
#if (TC_OSTHREADENUMERATE_1_EN)
void Irq_osThreadEnumerate_1 (void) {
  osThreadId_t id[10];

  Isr_u32 = osThreadEnumerate(id, 10U);
}
#endif

/*=======0=========1=========2=========3=========4=========5=========6=========7=========8=========9=========0=========1====*/
/**
\brief Test case: TC_ThreadNew
\details
- Create threads with different priorities and pass NULL argument to them
- Create threads with different priorities and pass valid argument to them
*/
void TC_ThreadNew (void) {
#if (TC_THREADNEW_EN)
  uint32_t arg = 0xFF;

  Var_ThreadExec = 0;

  /* - Create threads with different priorities and pass NULL argument to them */
  ASSERT_TRUE (osKernelLock() == 0U);
  ASSERT_TRUE (osThreadNew(Th_Thr0, NULL, &Th_Thr0_attr) != NULL);
  ASSERT_TRUE (osThreadNew(Th_Thr1, NULL, &Th_Thr1_attr) != NULL);
  ASSERT_TRUE (osThreadNew(Th_Thr2, NULL, &Th_Thr2_attr) != NULL);
  ASSERT_TRUE (osThreadNew(Th_Thr3, NULL, &Th_Thr3_attr) != NULL);
  ASSERT_TRUE (osThreadNew(Th_Thr4, NULL, &Th_Thr4_attr) != NULL);
  ASSERT_TRUE (osThreadNew(Th_Thr5, NULL, &Th_Thr5_attr) != NULL);
  osKernelUnlock();

  /* Wait until all threads go into inactive state */
  osDelay (100);

  /* Check if they were all executed */
  ASSERT_TRUE (Var_ThreadExec == 6);
  Var_ThreadExec = 0;

  /* - Create threads with different priorities and pass valid argument to them */
  ASSERT_TRUE (osKernelLock() == 0U);
  ASSERT_TRUE (osThreadNew(Th_Thr0, &arg, &Th_Thr0_attr) != NULL);
  ASSERT_TRUE (osThreadNew(Th_Thr1, &arg, &Th_Thr1_attr) != NULL);
  ASSERT_TRUE (osThreadNew(Th_Thr2, &arg, &Th_Thr2_attr) != NULL);
  ASSERT_TRUE (osThreadNew(Th_Thr3, &arg, &Th_Thr3_attr) != NULL);
  ASSERT_TRUE (osThreadNew(Th_Thr4, &arg, &Th_Thr4_attr) != NULL);
  ASSERT_TRUE (osThreadNew(Th_Thr5, &arg, &Th_Thr5_attr) != NULL);
  osKernelUnlock();

  /* Wait until all threads go into inactive state */
  osDelay (100);

  /* Check if they were all executed */
  ASSERT_TRUE (Var_ThreadExec == 12);

  /* Creating thread with invalid priority should fail */
  ASSERT_TRUE (osThreadNew (Th_Thr6, NULL, &Th_Thr6_attr) == NULL);
  ASSERT_TRUE (osThreadNew (Th_Thr6, &arg, &Th_Thr6_attr) == NULL);
#endif
}

/*=======0=========1=========2=========3=========4=========5=========6=========7=========8=========9=========0=========1====*/
/**
\brief Test case: TC_ThreadMultiInstance
\details
- Synchronise on time slice
- Create all defined instances of a thread
- Verify each instance id
- Wait until all instances executed
- Verify execution variable
*/
void TC_ThreadMultiInstance (void) {
#if (TC_THREADMULTIINSTANCE_EN)
  osThreadAttr_t attr = { NULL, osThreadDetached, NULL, 0U, NULL, 0U, osPriorityNormal, 0U, 0U};
  uint8_t    cnt[5];
  uint32_t   i;
  osThreadId_t id[5];

  /* Init counter array */
  for (i = 0; i < 5; i++) {
    cnt[i] = 0;
  }

  /* - Synchronise on time slice */
  osDelay (1);

  /* - Create all defined instances of a thread */
  for (i = 0; i < 5; i++) {
    id[i] = osThreadNew (Th_ThreadMultiInstance, &cnt[i], &attr);
    /* - Verify each instance id */
    ASSERT_TRUE (id[i] != NULL);
  }

  /* - Wait until all instances executed */
  osDelay (100);

  /* - Verify execution variable */
  for (i = 0; i < 5; i++) {
    ASSERT_TRUE (cnt[i] == 1);
  }
#endif
}

/*-----------------------------------------------------------------------------
 * TC_ThreadMultiInstance: Helper thread
 *----------------------------------------------------------------------------*/
#if (TC_THREADMULTIINSTANCE_EN)
void Th_ThreadMultiInstance (void *arg) {
  uint8_t *var = (uint8_t *)arg;
  (*var)++;
  osDelay(10);

  /* Explicitly terminate this thread */
  osThreadTerminate (osThreadGetId());
}
#endif

/*=======0=========1=========2=========3=========4=========5=========6=========7=========8=========9=========0=========1====*/
/**
\brief Test case: TC_ThreadTerminate
\details
- Initialize global counter variable to zero
- Create and run a test thread which increments a global counter
- Terminate test thread and remember counter value
- Wait and verify that thread is terminated by checking global counter
- Restart a thread and repeat the procedure
- Counter must not increment after test thread is terminated
*/
void TC_ThreadTerminate (void) {
#if (TC_THREADTERMINATE_EN)
  osThreadAttr_t attr = { NULL, osThreadDetached, NULL, 0U, NULL, 0U, osPriorityNormal, 0U, 0U};
  osThreadId_t id;
  uint32_t i, cnt;

  for (i = 0; i < 2; i++) {
    /* - Initialize global counter variable to zero */
    Var_Counter = 0;

    /* - Create and run a test thread which increments a global counter */
    id = osThreadNew (Th_CountingThread, NULL, &attr);
    ASSERT_TRUE (id != NULL);

    if (id != NULL) {
      /* Allow counting thread to run */
      ASSERT_TRUE (osDelay(5) == osOK);
      /* - Terminate test thread and remember counter value */
      ASSERT_TRUE (osThreadTerminate (id) == osOK);
      ASSERT_TRUE (Var_Counter != 0);
      cnt = Var_Counter;

      ASSERT_TRUE (osDelay(5) == osOK);
      /* - Wait and verify that thread is terminated by checking global counter */
      ASSERT_TRUE (cnt == Var_Counter);
    }
  }
#endif
}

/*=======0=========1=========2=========3=========4=========5=========6=========7=========8=========9=========0=========1====*/
/**
\brief Test case: TC_ThreadRestart
\details
- Create a counting thread and verify that it runs
- Terminate counting thread
- Recreate a counting thread and verify that is runs again
*/
void TC_ThreadRestart (void) {
#if (TC_THREADRESTART_EN)
  osThreadAttr_t attr = { NULL, osThreadDetached, NULL, 0U, NULL, 0U, osPriorityNormal, 0U, 0U};
  osThreadId_t id;
  uint32_t cnt, iter;

  /* Initalize global counter variable to zero */
  Var_Counter = 0;

  cnt  = 0;
  iter = 0;
  while (iter++ < 2) {
    /* - Create a counting thread and verify that it runs */
    id = osThreadNew (Th_CountingThread, NULL, &attr);
    ASSERT_TRUE (id != NULL);

    if (id != NULL) {
      /* Allow counting thread to run */
      ASSERT_TRUE (osDelay(5) == osOK);
      ASSERT_TRUE (osThreadTerminate (id) == osOK);

      if (iter == 1) {
        ASSERT_TRUE (Var_Counter != 0);
        cnt = Var_Counter;
      }
      else {
        ASSERT_TRUE (Var_Counter > cnt);
      }
    }
  }
#endif
}

/*=======0=========1=========2=========3=========4=========5=========6=========7=========8=========9=========0=========1====*/
/**
\brief Test case: TC_ThreadPriorityExec
\details
- Raise main thread priority to osPriorityRealtime
- Create multiple instances of the test thread
- Set instance priorities from low to realtime
- Lower main thread priority to allow execution of test threads
- Check if threads were executed according to their priorities
*/
void TC_ThreadPriorityExec (void) {
#if (TC_THREADPRIORITYEXEC_EN)
  osThreadAttr_t attr = { NULL, osThreadDetached, NULL, 0U, NULL, 0U, osPriorityLow, 0U, 0U};
  uint32_t i,j;
  osThreadId_t main_id, inst[6];

  main_id = osThreadGetId();
  ASSERT_TRUE (main_id != NULL);

  if (main_id != NULL) {
    /* - Raise main thread priority to osPriorityRealtime */
    ASSERT_TRUE (osThreadSetPriority (main_id, osPriorityRealtime) == osOK);

    /* - Create multiple instances of the test thread */
    inst[0] = osThreadNew (Th_ThreadPriorityExec, (void *)&inst[0], &attr);
    inst[1] = osThreadNew (Th_ThreadPriorityExec, (void *)&inst[1], &attr);
    inst[2] = osThreadNew (Th_ThreadPriorityExec, (void *)&inst[2], &attr);
    inst[3] = osThreadNew (Th_ThreadPriorityExec, (void *)&inst[3], &attr);
    inst[4] = osThreadNew (Th_ThreadPriorityExec, (void *)&inst[4], &attr);
    inst[5] = osThreadNew (Th_ThreadPriorityExec, (void *)&inst[5], &attr);

    for (i = 0; i < 6; i++) {
      ASSERT_TRUE (inst[i] != NULL);
      if (inst[i] == NULL) {
        /* Abort test if thread instance not created */
        return;
      }
      /* Check if the instances are different */
      for (j = 0; j < 6; j++) {
        if (i != j) {
            ASSERT_TRUE (inst[i] != inst[j]);
        }
      }
    }

    /* Clear execution array */
    for (i = 0; i < 6; i++) {
      ExecArr[i] = 0;
    }

    /* - Set instance priorities from low to realtime */
    ASSERT_TRUE (osThreadSetPriority (inst[0], osPriorityLow)         == osOK);
    ASSERT_TRUE (osThreadSetPriority (inst[1], osPriorityBelowNormal) == osOK);
    ASSERT_TRUE (osThreadSetPriority (inst[2], osPriorityNormal)      == osOK);
    ASSERT_TRUE (osThreadSetPriority (inst[3], osPriorityAboveNormal) == osOK);
    ASSERT_TRUE (osThreadSetPriority (inst[4], osPriorityHigh)        == osOK);
    ASSERT_TRUE (osThreadSetPriority (inst[5], osPriorityRealtime)    == osOK);

    /* - Lower main thread priority to allow execution of test threads */
    ASSERT_TRUE (osThreadSetPriority (main_id, osPriorityLow)         == osOK);
    ASSERT_TRUE (osThreadYield () == osOK);

    /* - Check if threads were executed according to their priorities */
    for (i = 0; i < 6; i++) {
      ASSERT_TRUE (ExecArr[i] == inst[6 - 1 - i]);
    }
  }
  /* - Restore main thread priority to osPriorityNormal */
  ASSERT_TRUE (osThreadSetPriority (main_id, osPriorityNormal) == osOK);
#endif
}

/*-----------------------------------------------------------------------------
 * TC_ThreadPriorityExec: Helper thread
 *----------------------------------------------------------------------------*/
#if (TC_THREADPRIORITYEXEC_EN)
void Th_ThreadPriorityExec (void *arg) {
  uint32_t i;
  for (i = 0; i < 7; i++) {
    if (ExecArr[i] == 0) {
      ExecArr[i] = *(osThreadId_t *)arg;
      break;
    }
  }

  /* Explicitly terminate this thread */
  osThreadTerminate (osThreadGetId());
}
#endif

/*=======0=========1=========2=========3=========4=========5=========6=========7=========8=========9=========0=========1====*/
/**
\brief Test case: TC_ThreadYield
\details
- Raise priority of the main thread
- Create child thread instances with normal priority
- Lower priority of the main thread to allow child threads to run
- When child threads terminate, check counter values
- Restore priority of the main thread
*/
void TC_ThreadYield (void) {
#if (TC_THREADYIELD_EN)
  osThreadAttr_t attr = { NULL, osThreadDetached, NULL, 0U, NULL, 0U, osPriorityNormal, 0U, 0U};
  uint32_t i, j, limit;
  uint32_t cnt;
  YIELD_TEST cfg[3];
  osThreadId_t id_main, id[3];

  /* Get main thread id */
  id_main = osThreadGetId();
  ASSERT_TRUE(id_main != NULL);

  /* Raise priority of the main thread */
  ASSERT_TRUE (osThreadSetPriority (id_main, osPriorityHigh) == osOK);

  limit = sizeof(cfg) / sizeof(cfg[0]);

  /* Initialize test structure */
  for (i = 0U; i < limit; i++) {
    cfg[i].Cnt    = (uint32_t *)&cnt;
    cfg[i].Res[0] = 0U;
    cfg[i].Res[1] = 0U;
  }
  /* Initialize test counter */
  cnt = 0;

  /* - Create instances of the same thread */
  for (i = 0U; i < limit; i++) {
    id[i] = osThreadNew (Th_YieldTest, &cfg[i], &attr);
    ASSERT_TRUE (id[i] != NULL);
  }

  /* Check if threads id are different */
  for (i = 0U; i < limit; i++) {
    for (j = 0U; j < limit; j++) {
      if (i != j) {
        ASSERT_TRUE (id[i] != id[j]);
      }
    }
  }

  /* Lower priority of the main thread to allow child threads to run */
  ASSERT_TRUE (osThreadSetPriority (id_main, osPriorityLow) == osOK);

  /* Child threads shall be terminated, check expected counter values */
  for (i = 0U; i < limit; i++) {
    /* Results will be the same in case if yield is not functioning */
    ASSERT_TRUE (cfg[i].Res[0] != cfg[i].Res[1]);
  }

  /* Restore priority of the main thread back to normal */
  ASSERT_TRUE (osThreadSetPriority (id_main, osPriorityNormal) == osOK);
#endif
}

/*-----------------------------------------------------------------------------
 * TC_ThreadYield: Helper thread
 *----------------------------------------------------------------------------*/
#if (TC_THREADYIELD_EN)
void Th_YieldTest (void *arg) {
  YIELD_TEST *cfg = (YIELD_TEST *)arg;

  *cfg->Cnt  += 1;
  cfg->Res[0] = *cfg->Cnt;

  ASSERT_TRUE (osThreadYield() == osOK);

  cfg->Res[1] = *cfg->Cnt;
  *cfg->Cnt  += 1;

  ASSERT_TRUE (osThreadYield() == osOK);

  /* Explicitly terminate this thread */
  osThreadTerminate (osThreadGetId());
}
#endif

/*=======0=========1=========2=========3=========4=========5=========6=========7=========8=========9=========0=========1====*/
/**
\brief Test case: TC_ThreadSuspendResume
\details
- Test thread suspend and resume
*/
void TC_ThreadSuspendResume (void) {
#if (TC_THREADSUSPENDRESUME_EN)
  osThreadAttr_t attr = { NULL, osThreadDetached, NULL, 0U, NULL, 0U, osPriorityBelowNormal, 0U, 0U};
  osThreadId_t id;
  int32_t cnt = 0;

  /* - Create a thread */
  id = osThreadNew (Th_SuspendResume, &cnt, &attr);
  ASSERT_TRUE(id != NULL);
  osDelay(10);

  /* - Resume thread and check counter */
  ASSERT_TRUE(osThreadResume(id) == osOK);
  osDelay(10);
  ASSERT_TRUE(cnt == 1);

  /* - Resume thread and check counter */
  ASSERT_TRUE(osThreadResume(id) == osOK);
  osDelay(10);
  ASSERT_TRUE(cnt == 2);
#endif
}

/*-----------------------------------------------------------------------------
 * TC_ThreadSuspendResume: Helper thread
 *----------------------------------------------------------------------------*/
#if (TC_THREADSUSPENDRESUME_EN)
void Th_SuspendResume (void *arg) {
  int32_t *cnt = (int32_t *)arg;
  osThreadId_t id = osThreadGetId();

  /* Suspend thread */
  ASSERT_TRUE(osThreadSuspend(id) == osOK);
  (*cnt)++;

  /* Suspend thread */
  ASSERT_TRUE(osThreadSuspend(id) == osOK);
  (*cnt)++;

  /* Explicitly terminate this thread */
  osThreadTerminate (osThreadGetId());
}
#endif

/*=======0=========1=========2=========3=========4=========5=========6=========7=========8=========9=========0=========1====*/
/**
\brief Test case: TC_ThreadReturn
\details
- Test thread return
*/
void TC_ThreadReturn (void) {
#if (TC_THREADRETURN_EN)
  osThreadAttr_t attr = { NULL, osThreadDetached, NULL, 0U, NULL, 0U, osPriorityLow, 0U, 0U};
  osThreadId_t id;
  osStatus_t stat;

  /* Create a child thread that terminates by just returning */
  id = osThreadNew (Th_ThreadReturn, NULL, &attr);
  ASSERT_TRUE (id != NULL);

  osDelay(10);

  /* - Try to terminate */
  stat = osThreadTerminate(id);
  ASSERT_TRUE((stat == osErrorParameter)||(stat == osErrorResource));
#endif
}

/*-----------------------------------------------------------------------------
 * TC_ThreadReturn: Helper thread
 *----------------------------------------------------------------------------*/
#if (TC_THREADRETURN_EN)
void Th_ThreadReturn (void *arg) {
  (void)arg;

  return;
}
#endif

/*=======0=========1=========2=========3=========4=========5=========6=========7=========8=========9=========0=========1====*/
/**
\brief Test case: TC_ThreadAllocation
\details
- Test thread object allocation
*/
void TC_ThreadAllocation (void) {
#if (TC_THREADALLOCATION_EN)
  osThreadAttr_t attr = { NULL, osThreadDetached, NULL, 0U, NULL, 0U, osPriorityLow, 0U, 0U};
  osThreadId_t id[MAX_THREAD_NUM];
  uint32_t cnt = 0U;
  uint32_t max = 0U;
  uint32_t i;

  /* Create max number of objects */
  for (i = 0U; i < MAX_THREAD_NUM; i++) {
    id[i] = osThreadNew (Th_Run, NULL, &attr);

    if (id[i] == NULL) {
      max = i;
      break;
    }
  }
  ASSERT_TRUE (i > 0U);

  if (max > 0U) {
    /* Try to allocate extra object */
    ASSERT_TRUE(osThreadNew (Th_Run, NULL, &attr) == NULL);
  }

  osDelay(10U);

  /* Terminate all */
  cnt = i;

  for (i = 0U; i < cnt; i++) {
    ASSERT_TRUE(osThreadTerminate(id[i]) == osOK);
  }
#endif
}

/**
@}
*/
// end of group thread_funcs
