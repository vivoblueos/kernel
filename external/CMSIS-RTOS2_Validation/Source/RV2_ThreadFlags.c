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

/* Definitions for signaling thread */
#define TST_SIG_CHILD 1                 /* Test child thread signaling        */
#define TST_SIG_ISR   2                 /* Test ISR signaling                 */

#define THREAD_FLAGS_MSK ((1U << MAX_THREADFLAGS_CNT) - 1)

void Th_ChildSignals (void *arg);
void Th_Sig          (void *arg);
void Th_Sig_Wakeup   (void *arg);
void Th_Sig_Child_0  (void *arg);
void Th_Sig_Child_1  (void *arg);
void Th_SignalSet    (void *arg);

void ThreadFlags_IRQHandler (void);


/*-----------------------------------------------------------------------------
 * Signaling thread
 *----------------------------------------------------------------------------*/
void Th_Sig (void *arg) {
  uint32_t typ = *(uint32_t *)arg;
  uint32_t flags;
  uint32_t flag;

  flag = 0x00000001U;
  switch (typ) {
    case TST_SIG_CHILD:
      do {
        /* Wait 100ms for signals from the main thread */
        flags = osThreadFlagsWait (flag, 0, 100);
        ASSERT_TRUE (flags == flag);

        if (flags == flag) {

          if (flag <= THREAD_FLAGS_MSK) {
            /* Send signal back to the main thread */
            ASSERT_TRUE ((int32_t)osThreadFlagsSet(ThreadId, flag) >= 0);
            flag <<= 1;
          }
        }
      }
      while ((flags > 0U) && (flag <= THREAD_FLAGS_MSK));
      osThreadFlagsWait (1U, 0, osWaitForever);
      break;
  }

  /* Explicitly terminate this thread */
  osThreadTerminate (osThreadGetId());
}

/*-----------------------------------------------------------------------------
 *      Wakeup thread
 *----------------------------------------------------------------------------*/
void Th_Sig_Wakeup (void __attribute__((unused)) *arg)
{
  osDelay(10);
  /* Send signal back to the main thread */
  ASSERT_TRUE (osThreadFlagsSet (ThreadId, 1U) == 0U);

  /* Explicitly terminate this thread */
  osThreadTerminate (osThreadGetId());
}

/*-----------------------------------------------------------------------------
 *      Default IRQ Handler
 *----------------------------------------------------------------------------*/
void ThreadFlags_IRQHandler (void) {
  switch (Isr_s32) {
    case 0: Isr_u32 = osThreadFlagsSet   (ThreadId, 0x00000001U);     break;
    case 1: Isr_u32 = osThreadFlagsClear (0x00000001U);                   break;
    case 2: Isr_u32 = osThreadFlagsWait  (0x00000001U, 0,             0); break;
    case 3: Isr_u32 = osThreadFlagsWait  (0x00000001U, 0,           100); break;
    case 4: Isr_u32 = osThreadFlagsWait  (0x00000001U, 0, osWaitForever); break;
  }
}

/*-----------------------------------------------------------------------------
 * Signal setting thread
 *----------------------------------------------------------------------------*/
void Th_SignalSet (void *arg) {
  uint32_t flags = *(uint32_t *)arg;
  osThreadFlagsSet (ThreadId, flags);

  /* Explicitly terminate this thread */
  osThreadTerminate (osThreadGetId());
}

/*-----------------------------------------------------------------------------
 * Child signals thread
 *----------------------------------------------------------------------------*/
void Th_ChildSignals (void __attribute__((unused)) *arg) {
  uint32_t flags, set, clr;
  osThreadId_t t_id = osThreadGetId();

  ASSERT_TRUE (t_id != NULL);

  if (t_id != NULL) {
    /* - Set all signal flags */
    flags = 0x00000000U;
    set   = 0x00000001U;
    do {
      ASSERT_TRUE (osThreadFlagsSet (t_id, set) > 0U);
      flags = (flags << 1) | 1U;
      set <<= 1;
    }
    while (set <= THREAD_FLAGS_MSK);

    /* MSB flag cannot be set by user */
    flags = osThreadFlagsSet (t_id, 0x80000000U);
    ASSERT_TRUE (flags == (uint32_t)osErrorParameter);

    /* - Clear all thread flags */
    flags = THREAD_FLAGS_MSK;
    clr   = (1U << (MAX_THREADFLAGS_CNT - 1));
    do {
      ASSERT_TRUE (osThreadFlagsClear (clr) == flags);
      clr   >>= 1;
      flags >>= 1;
    }
    while (clr);
  }

  /* Explicitly terminate this thread */
  osThreadTerminate (osThreadGetId());
}

/*-----------------------------------------------------------------------------
 * Signal to Child 0 thread
 *----------------------------------------------------------------------------*/
void Th_Sig_Child_0 (void *arg) {
  osThreadId_t *id = (osThreadId_t *)arg;
  uint32_t flags;
  uint32_t flag;

  if (id != NULL) {
    flag = 1U;
    do {
      osThreadFlagsSet (*id, flag);
      /* - Wait for signals sent from Child 1 */
      flags = osThreadFlagsWait (flag, 0, 100);
      ASSERT_TRUE (flags > 0U);

      flag <<= 1;
      flag  |= (flag & 2U) ? (0U) : (1U);
    }
    while ((flags > 0U) && (flag <= THREAD_FLAGS_MSK));
  }
  osThreadFlagsSet (ThreadId, 1U);

  /* Explicitly terminate this thread */
  osThreadTerminate (osThreadGetId());
}

/*-----------------------------------------------------------------------------
 * Signal to Child 1 thread
 *----------------------------------------------------------------------------*/
void Th_Sig_Child_1 (void *arg) {
  osThreadId_t *id = (osThreadId_t *)arg;
  uint32_t flags;
  uint32_t flag;

  if (id != NULL) {
    flag = 1U;
    do {
      /* - Wait for signals sent from sender */
      flags = osThreadFlagsWait (flag, 0, 100);
      ASSERT_TRUE (flags > 0U);

      /* - Send received signal mask back to sender */
      osThreadFlagsSet (*id, flag);

      flag <<= 1;
      flag  |= (flag & 2U) ? (0U) : (1U);
    }
    while ((flags > 0U) && (flag <= THREAD_FLAGS_MSK));
  }
  osThreadFlagsSet (ThreadId, 0x02U);

  /* Explicitly terminate this thread */
  osThreadTerminate (osThreadGetId());
}

/*-----------------------------------------------------------------------------
 *      Test cases
 *----------------------------------------------------------------------------*/

/*=======0=========1=========2=========3=========4=========5=========6=========7=========8=========9=========0=========1====*/
/**
\defgroup threadflags_funcs Thread Flags Functions
\brief Thread Flags Functions Test Cases
\details
The test cases check the Thread Flags functions.

@{
*/

/*=======0=========1=========2=========3=========4=========5=========6=========7=========8=========9=========0=========1====*/
/**
\brief Test case: TC_ThreadFlagsMainThread
\details
- Set all thread flags for the main thread
- Clear all thread flags for the main thread
*/
void TC_ThreadFlagsMainThread (void) {
#if (TC_THREADFLAGSMAINTHREAD_EN)
  uint32_t flags, set, clr;
  osThreadId_t t_id = osThreadGetId();

  ASSERT_TRUE (t_id != NULL);

  if (t_id != NULL) {
    /* Clear thread flags */
    osThreadFlagsClear (THREAD_FLAGS_MSK);

    /* Set all thread flags */
    flags = 0x00000000U;
    set   = 0x00000001U;
    do {
      flags = (flags << 1) | 1U;
      ASSERT_TRUE (osThreadFlagsSet (t_id, set) == flags);
      set <<= 1;
    }
    while (set <= THREAD_FLAGS_MSK);

    /* Clear all thread flags */
    flags = THREAD_FLAGS_MSK;
    clr   = (1U << (MAX_THREADFLAGS_CNT - 1));
    do {
      ASSERT_TRUE (osThreadFlagsClear (clr) == flags);
      clr   >>= 1;
      flags >>= 1;
    }
    while (clr);
  }
#endif
}


/*=======0=========1=========2=========3=========4=========5=========6=========7=========8=========9=========0=========1====*/
/**
\brief Test case: TC_ThreadFlagsChildThread
\details
- Create a child thread
  Within child thread:
- Verify that all flags are cleared
- Set all thread flags
- Verify that all thread flags are set
- Clear all thread flags
- Verify that all thread flags are cleared
*/
void TC_ThreadFlagsChildThread (void) {
#if (TC_THREADFLAGSCHILDTHREAD_EN)
  osThreadAttr_t attr = { NULL, osThreadDetached, NULL, 0U, NULL, 0U, osPriorityNormal, 0U, 0U};

  ASSERT_TRUE (osThreadNew (Th_ChildSignals, NULL, &attr) != NULL);

  /* Wait for thread to terminate */
  osDelay(2U);
#endif
}

/*=======0=========1=========2=========3=========4=========5=========6=========7=========8=========9=========0=========1====*/
/**
\brief Test case: TC_ThreadFlagsChildToParent
\details
- Create signaling thread
- Send signal to the signaling thread
*/
void TC_ThreadFlagsChildToParent (void) {
#if (TC_THREADFLAGSCHILDTOPARENT_EN)
  osThreadAttr_t attr = { NULL, osThreadDetached, NULL, 0U, NULL, 0U, osPriorityBelowNormal, 0U, 0U};
  osThreadId_t id;
  uint32_t arg  = TST_SIG_CHILD;
  uint32_t flag;

  /* Get main thread ID */
  ThreadId = osThreadGetId();
  ASSERT_TRUE (ThreadId != NULL);

  if (ThreadId != NULL) {
    /* Create signaling thread */
    id = osThreadNew (Th_Sig, &arg, &attr);
    ASSERT_TRUE (id != NULL);

    if (id != NULL) {
      flag = 0x00000001U;
      do {
        /* Send signal to the signaling thread */
        ASSERT_TRUE ((int32_t)osThreadFlagsSet(id, flag) >= 0);

        if (flag <= THREAD_FLAGS_MSK) {
          ASSERT_TRUE (osThreadFlagsWait (flag, 0, 100) > 0U);
        }
        flag <<= 1;
      }
      while(flag <= THREAD_FLAGS_MSK);
      /* Terminate signaling thread */
      ASSERT_TRUE (osThreadTerminate (id) == osOK);
    }
  }
#endif
}

/*=======0=========1=========2=========3=========4=========5=========6=========7=========8=========9=========0=========1====*/
/**
\brief Test case: TC_ThreadFlagsChildToChild
\details
- Create two child threads
  Within child thread:
- Verify that all flags are cleared
- Set all thread flags
- Verify that all thread flags are set
- Clear all thread flags
- Verify that all thread flags are cleared
*/
void TC_ThreadFlagsChildToChild (void) {
#if (TC_THREADFLAGSCHILDTOCHILD_EN)
  osThreadAttr_t attr = { NULL, osThreadDetached, NULL, 0U, NULL, 0U, osPriorityBelowNormal, 0U, 0U};
  osThreadId_t id[2];

  ThreadId = osThreadGetId();
  ASSERT_TRUE (ThreadId != NULL);

  if (ThreadId != NULL) {
    id[0] = osThreadNew (Th_Sig_Child_0, &id[1], &attr);
    id[1] = osThreadNew (Th_Sig_Child_1, &id[0], &attr);

    ASSERT_TRUE (id[0] != NULL);
    ASSERT_TRUE (id[1] != NULL);

    /* - Wait for signals from child threads */
    ASSERT_TRUE (osThreadFlagsWait (0x03U, osFlagsWaitAll, 100) == 0x03U);

    osThreadTerminate(id[0]);
    osThreadTerminate(id[1]);
  }
#endif
}

/*=======0=========1=========2=========3=========4=========5=========6=========7=========8=========9=========0=========1====*/
/**
\brief Test case: TC_ThreadFlagsWaitTimeout
\details
- Clear all flags for current thread
- Wait for any single flag without timeout
- Wait for any single flag with timeout
- Wait for all flags without timeout
- Wait for all flags with timeout
- Wait for various flag masks from a signaling thread
*/
void TC_ThreadFlagsWaitTimeout (void) {
#if (TC_THREADFLAGSWAITTIMEOUT_EN)
  osThreadAttr_t attr = { NULL, osThreadDetached, NULL, 0U, NULL, 0U, osPriorityNormal, 0U, 0U};
  osThreadId_t id;
  uint32_t   flags;

  ThreadId = osThreadGetId();
  ASSERT_TRUE (ThreadId != NULL);

  if (ThreadId != NULL) {
    /* - Clear all signals for current thread */
    osThreadFlagsClear (THREAD_FLAGS_MSK);

    /* - Wait for any single signal without timeout */
    ASSERT_TRUE (osThreadFlagsWait (THREAD_FLAGS_MSK, osFlagsWaitAny, 0) == (uint32_t)osErrorResource);
    /* - Wait for any single signal with timeout */
    ASSERT_TRUE (osThreadFlagsWait (THREAD_FLAGS_MSK, osFlagsWaitAny, 5) == (uint32_t)osErrorTimeout);
    /* - Wait for all signals without timeout */
    ASSERT_TRUE (osThreadFlagsWait (THREAD_FLAGS_MSK, osFlagsWaitAll, 0) == (uint32_t)osErrorResource);
    /* - Wait for all signals with timeout */
    ASSERT_TRUE (osThreadFlagsWait (THREAD_FLAGS_MSK, osFlagsWaitAll, 5) ==(uint32_t)osErrorTimeout);

    /* - Create a signal setting thread */
    flags = 3U;
    id = osThreadNew (Th_SignalSet, &flags, &attr);
    ASSERT_TRUE (id != NULL);

    if (id != NULL) {
      osDelay(5);

      /* - Wait for various signal masks from a signaling thread */
      ASSERT_TRUE (osThreadFlagsWait (1U, 0, 10) == 3U);
    }
    osDelay(10);

    /* - Create a signal setting thread */
    flags = 5U;
    id = osThreadNew (Th_SignalSet, &flags, &attr);
    ASSERT_TRUE (id != NULL);

    if (id != NULL) {
      osDelay(5);

      /* - Wait for various signal masks from a signaling thread */
      ASSERT_TRUE (osThreadFlagsWait (2U, 0, 10) == 7U);
    }
    osThreadFlagsClear (THREAD_FLAGS_MSK);
    osDelay(10);
  }
#endif
}

/*=======0=========1=========2=========3=========4=========5=========6=========7=========8=========9=========0=========1====*/
/**
\brief Test case: TC_ThreadFlagsCheckTimeout
\details
- Set time thresholds
- Create wakeup thread to set a thread flag after 10 ticks
- Wait for a thread flag with a defined timeout
- Check if the thread flag is raised between the minimum and maximum thresholds
- Wait for a thread flag with an infinite timeout
- Check if the thread flag is raised between the minimum and maximum thresholds
*/
void TC_ThreadFlagsCheckTimeout (void) {
#if (TC_THREADFLAGSCHECKTIMEOUT_EN)
  osThreadAttr_t attr = { NULL, osThreadDetached, NULL, 0U, NULL, 0U, osPriorityBelowNormal, 0U, 0U};
  osThreadId_t id;
  uint32_t flags;
  uint32_t t_10;

  /* Get main thread ID */
  ThreadId = osThreadGetId();
  ASSERT_TRUE (ThreadId != NULL);

  if (ThreadId != NULL) {
    /* Synchronize tick */
    osDelay(1U);

    /* Create wakeup thread to set a signal after 10 ticks */
    id = osThreadNew(Th_Sig_Wakeup, NULL, &attr);

    if (id != NULL) {
      t_10 = osKernelGetTickCount();
      flags = osThreadFlagsWait (1U, 0, 100);
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
    id = osThreadNew(Th_Sig_Wakeup, NULL, &attr);

    if (id != NULL) {
      t_10 = osKernelGetTickCount();
      flags = osThreadFlagsWait (1U, 0, osWaitForever);
      t_10 = osKernelGetTickCount() - t_10;

      ASSERT_TRUE (flags == 1U);
      ASSERT_TRUE (t_10 == 10U);
    }
    else {
      ASSERT_TRUE (id != NULL);
    }

    /* Wait until wakeup thread is terminated */
    osDelay(5U);
  }
#endif
}

/*=======0=========1=========2=========3=========4=========5=========6=========7=========8=========9=========0=========1====*/
/**
\brief Test case: TC_ThreadFlagsParam
\details
- Test flag management functions with invalid parameters
*/
void TC_ThreadFlagsParam (void) {
#if (TC_THREADFLAGSPARAM_EN)
  /* Test osThreadFlagsSet */
  ASSERT_TRUE (osThreadFlagsSet (NULL, 0) == (uint32_t)osErrorParameter);

  /* Flag mask with MSB set cannot be set by user */
  ASSERT_TRUE (osThreadFlagsSet (osThreadGetId(), 0x80000000U) == (uint32_t)osErrorParameter);

  /* Cannot wait for flag mask with MSB set */
  ASSERT_TRUE (osThreadFlagsWait  (0x80000000U, 0, 0) == (uint32_t)osErrorParameter);

  /* Cannot clear flag mask with MSB set */
  ASSERT_TRUE (osThreadFlagsClear (0x80000000U) == (uint32_t)osErrorParameter);
#endif
}

/*=======0=========1=========2=========3=========4=========5=========6=========7=========8=========9=========0=========1====*/
/**
\brief Test case: TC_ThreadFlagsInterrupts
\details
- Call all flag management functions from the ISR
*/
void TC_ThreadFlagsInterrupts (void) {
#if (TC_THREADFLAGSINTERRUPTS_EN)
  TST_IRQHandler = ThreadFlags_IRQHandler;

  ThreadId = osThreadGetId();
  ASSERT_TRUE (ThreadId != NULL);

  if (ThreadId != NULL) {
    /* Clear all main thread thread flags */
    osThreadFlagsClear (THREAD_FLAGS_MSK);

    /* Test signaling between ISR and main thread */

    Isr_s32 = 0; /* Test: osThreadFlagsSet */
    Isr_u32 = 0U;
    SetPendingIRQ(IRQ_A);
    ASSERT_TRUE (osThreadFlagsWait (0x00000001U, 0, 100) == 0x00000001U);
    ASSERT_TRUE (Isr_u32 == 0x00000001U);

    Isr_s32 = 1; /* Test: osThreadFlagsClear */
    Isr_u32 = 0U;
    ASSERT_TRUE (osThreadFlagsSet (ThreadId, 0x00000001U) == 0x00000001U);
    SetPendingIRQ(IRQ_A);
    ASSERT_TRUE (Isr_u32 == (uint32_t)osErrorISR);

    Isr_s32 = 2; /* Test: osThreadFlagsWait (no timeout) */
    Isr_u32 = 0U;
    SetPendingIRQ(IRQ_A);
    ASSERT_TRUE (Isr_u32 == (uint32_t)osErrorISR);

    Isr_s32 = 3; /* Test: osThreadFlagsWait (with timeout) */
    Isr_u32 = 0U;
    SetPendingIRQ(IRQ_A);
    ASSERT_TRUE (Isr_u32 == (uint32_t)osErrorISR);

    Isr_s32 = 4; /* Test: osThreadFlagsWait (with infinite timeout) */
    Isr_u32 = 0U;
    SetPendingIRQ(IRQ_A);
    ASSERT_TRUE (Isr_u32 == (uint32_t)osErrorISR);

    /* Clear all main thread thread flags */
    osThreadFlagsClear (THREAD_FLAGS_MSK);
  }
#endif
}

/**
@}
*/
// end of group threadflags_funcs
