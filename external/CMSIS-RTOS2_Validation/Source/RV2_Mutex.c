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
#define MAX_MUTEX_NUM  64

/* Definitions of shared variables */
static uint8_t G_ExecArr[3];             /* Global execution array      */

void Th_MutexWait        (void *arg);
void Th_MutexWakeup      (void *arg);
void Th_MutexHighPrioAcq (void *arg);
void Th_LowPrioJob       (void *arg);
void Th_MediumPrioJob    (void *arg);
void Th_HighPrioJob      (void *arg);
void Th_MutexAcqLow      (void *arg);
void Th_MutexRelHigh     (void *arg);
void Th_osMutexAcquire_2 (void *arg);

void Irq_osMutexNew_1      (void);
void Irq_osMutexGetName_1  (void);
void Irq_osMutexAcquire_1  (void);
void Irq_osMutexRelease_1  (void);
void Irq_osMutexGetOwner_1 (void);
void Irq_osMutexDelete_1   (void);

static void RecursiveMutexAcquire (uint32_t depth, uint32_t ctrl);
/*-----------------------------------------------------------------------------
 * Mutex high prio acquiring thread
 *----------------------------------------------------------------------------*/
#if (TC_MUTEXROBUST_EN) || (TC_MUTEXPRIOINHERIT_EN)
void Th_MutexHighPrioAcq (void *arg) {
  uint32_t *cnt = (uint32_t *)arg;
  ASSERT_TRUE (osMutexAcquire (MutexId, osWaitForever) == osOK);
  (*cnt)++;
  /* This call should never return */
  osThreadFlagsWait (1, 0, osWaitForever);
}
#endif

/*-----------------------------------------------------------------------------
 * Recursive mutex acquisition
 *----------------------------------------------------------------------------*/
static void RecursiveMutexAcquire (uint32_t depth, uint32_t ctrl) {
  static uint32_t acq;                  /* Mutex acquisition counter          */
  osStatus_t stat;

  /* Acquire a mutex */
  stat = osMutexAcquire (MutexId, 100);
  ASSERT_TRUE (stat == osOK);

  if (stat == osOK) {
    if (ctrl == depth) {
      /* - Verify that mutex was acquired at count zero */
      ASSERT_TRUE (acq == 0);
    }
    acq++;

    if (depth) {
      RecursiveMutexAcquire (depth - 1, ctrl);
    }
    acq--;

    /* Release a mutex */
    stat = osMutexRelease (MutexId);
    ASSERT_TRUE (stat == osOK);
  }
}

/*-----------------------------------------------------------------------------
 * Thread waiting for mutex with MutexId
 *----------------------------------------------------------------------------*/
void Th_MutexWait (void __attribute__((unused)) *arg) {
  RecursiveMutexAcquire (3, 3);

  /* Explicitly terminate this thread */
  osThreadTerminate (osThreadGetId());
}

/*-----------------------------------------------------------------------------
 *      Wakeup thread
 *----------------------------------------------------------------------------*/
void Th_MutexWakeup (void __attribute__((unused)) *arg)
{
  /* Acquire mutex */
  ASSERT_TRUE (osMutexAcquire (MutexId, 0) == osOK);

  osDelay(10);

  /* Release mutex to the main thread */
  ASSERT_TRUE (osMutexRelease (MutexId) == osOK);

  /* Explicitly terminate this thread */
  osThreadTerminate (osThreadGetId());
}

/*-----------------------------------------------------------------------------
 * Low priority job used for priority inversion test
 *----------------------------------------------------------------------------*/
#if (TC_MUTEXPRIORITYINVERSION_EN)
void Th_LowPrioJob (void *arg) {
  osThreadId_t *ctrl_id = (osThreadId_t *)arg;
  osStatus_t stat;
  uint32_t i;

  /* Obtain a mutex object */
  stat = osMutexAcquire (MutexId, 0);
  ASSERT_TRUE (stat == osOK);

  if (stat == osOK) {
    /* Mutex acquired, inform control thread */
    osThreadFlagsSet (*ctrl_id, (1 << 0));

    /* Set mark into execution array */
    for (i = 0; i < 3; i++) {
      if (G_ExecArr[i] == 0) {
        G_ExecArr[i] = 'L';             /* L as Low priority job              */

        /* Inform control thread */
        osThreadFlagsSet (*ctrl_id, (1 << 1));
        break;
      }
    }
    ASSERT_TRUE (osMutexRelease (MutexId) == osOK);
  }

  /* Explicitly terminate this thread */
  osThreadTerminate (osThreadGetId());
}
#endif

/*-----------------------------------------------------------------------------
 * Medium priority job used for priority inversion test
 *----------------------------------------------------------------------------*/
#if (TC_MUTEXPRIORITYINVERSION_EN)
void Th_MediumPrioJob (void *arg) {
  osThreadId_t *ctrl_id = (osThreadId_t *)arg;
  uint32_t i;

  /* Set mark into execution array */
  for (i = 0; i < 3; i++) {
    if (G_ExecArr[i] == 0) {
      G_ExecArr[i] = 'M';             /* M as Medium priority job           */

      /* Inform control thread */
      osThreadFlagsSet (*ctrl_id, (1 << 2));
      break;
    }
  }

  /* Explicitly terminate this thread */
  osThreadTerminate (osThreadGetId());
}
#endif

/*-----------------------------------------------------------------------------
 * High priority job used for priority inversion test
 *----------------------------------------------------------------------------*/
#if (TC_MUTEXPRIORITYINVERSION_EN)
void Th_HighPrioJob (void *arg) {
  osThreadId_t *ctrl_id = (osThreadId_t *)arg;
  osStatus_t stat;
  uint32_t i;

  /* Allow control thread to be executed while this thread waits */
  osThreadFlagsSet (*ctrl_id, 1);

  /* Wait for a mutex object */
  stat = osMutexAcquire (MutexId, 200);
  ASSERT_TRUE (stat == osOK);

  if (stat == osOK) {
    /* Set mark into execution array */
    for (i = 0; i < 3; i++) {
      if (G_ExecArr[i] == 0) {
        G_ExecArr[i] = 'H';             /* H as High priority job             */

        /* Inform control thread */
        osThreadFlagsSet (*ctrl_id, (1 << 3));
        break;
      }
    }
    ASSERT_TRUE (osMutexRelease (MutexId) == osOK);
  }

  /* Explicitly terminate this thread */
  osThreadTerminate (osThreadGetId());
}
#endif

/*-----------------------------------------------------------------------------
 * Low priority thread which acquires a mutex object
 *----------------------------------------------------------------------------*/
#if (TC_MUTEXOWNERSHIP_EN)
void Th_MutexAcqLow  (void __attribute__((unused)) *arg) {
  ASSERT_TRUE (osMutexAcquire (MutexId, 0) == osOK);
  osThreadFlagsWait (1, 0, 100);
  ASSERT_TRUE (osMutexRelease (MutexId) == osOK);
  /* This call should never return */
  osThreadFlagsWait (1, 0, osWaitForever);
}
#endif

/*-----------------------------------------------------------------------------
 * High priority thread which releases a mutex object
 *----------------------------------------------------------------------------*/
#if (TC_MUTEXOWNERSHIP_EN)
void Th_MutexRelHigh (void __attribute__((unused)) *arg) {
  ASSERT_TRUE (osMutexRelease (MutexId) == osErrorResource);
  /* This call should never return */
  osThreadFlagsWait (1, 0, osWaitForever);
}
#endif

/*-----------------------------------------------------------------------------
 *      Test cases
 *----------------------------------------------------------------------------*/

/*=======0=========1=========2=========3=========4=========5=========6=========7=========8=========9=========0=========1====*/
/**
\defgroup mutex_func Mutex Functions
\brief Mutex Functions Test Cases
\details
The test cases check the osMutex* functions.

@{
*/

/*=======0=========1=========2=========3=========4=========5=========6=========7=========8=========9=========0=========1====*/
/**
\brief Test case: TC_osMutexNew_1
\details
  - Call osMutexNew to create a mutex object
  - Call osMutexNew from ISR
*/
void TC_osMutexNew_1 (void) {
#if (TC_OSMUTEXNEW_1_EN)
  osMutexId_t id;

  /* Call osMutexNew to create a mutex object */
  id = osMutexNew (NULL);
  ASSERT_TRUE (id != NULL);

  /* Delete created mutex */
  ASSERT_TRUE (osMutexDelete(id) == osOK);

  /* Call osMutexNew from ISR */
  TST_IRQHandler = Irq_osMutexNew_1;
  MutexId = (osMutexId_t)(-1);
  SetPendingIRQ(IRQ_A);
  ASSERT_TRUE (MutexId == NULL);
#endif
}

/*-----------------------------------------------------------------------------
 * TC_osMutexNew_1: ISR handler
 *----------------------------------------------------------------------------*/
#if (TC_OSMUTEXNEW_1_EN)
void Irq_osMutexNew_1 (void) {
  MutexId = osMutexNew (NULL);
}
#endif

/*=======0=========1=========2=========3=========4=========5=========6=========7=========8=========9=========0=========1====*/
/**
\brief Test case: TC_osMutexNew_2
\details
  - Call osMutexNew to create a recursive mutex object
*/
void TC_osMutexNew_2 (void) {
#if (TC_OSMUTEXNEW_2_EN)
  osMutexAttr_t attr = {NULL, osMutexRecursive, NULL, 0U};
  osMutexId_t id;

  /* Call osMutexNew to create a recursive mutex mutex object */
  id = osMutexNew (&attr);
  ASSERT_TRUE (id != NULL);

  /* Delete created mutex */
  ASSERT_TRUE (osMutexDelete(id) == osOK);
#endif
}

/*=======0=========1=========2=========3=========4=========5=========6=========7=========8=========9=========0=========1====*/
/**
\brief Test case: TC_osMutexNew_3
\details
  - Call osMutexNew to create a mutex object that uses priority inheritance protocol
*/
void TC_osMutexNew_3 (void) {
#if (TC_OSMUTEXNEW_3_EN)
  osMutexAttr_t attr = {NULL, osMutexPrioInherit, NULL, 0U};
  osMutexId_t id;

  /* Call osMutexNew to create a mutex object that uses priority inheritance protocol */
  id = osMutexNew (&attr);
  ASSERT_TRUE (id != NULL);

  /* Delete created mutex */
  ASSERT_TRUE (osMutexDelete(id) == osOK);
#endif
}

/*=======0=========1=========2=========3=========4=========5=========6=========7=========8=========9=========0=========1====*/
/**
\brief Test case: TC_osMutexNew_4
\details
  - Call osMutexNew to create a robust mutex object
*/
void TC_osMutexNew_4 (void) {
#if (TC_OSMUTEXNEW_4_EN)
  osMutexAttr_t attr = {NULL, osMutexRobust, NULL, 0U};
  osMutexId_t id;

  /* Call osMutexNew to create a robust mutex object */
  id = osMutexNew (&attr);
  ASSERT_TRUE (id != NULL);

  /* Delete created mutex */
  ASSERT_TRUE (osMutexDelete(id) == osOK);
#endif
}

/*=======0=========1=========2=========3=========4=========5=========6=========7=========8=========9=========0=========1====*/
/**
\brief Test case: TC_osMutexNew_5
\details
  - Call osMutexNew to create mutex object and assign a name to it
*/
void TC_osMutexNew_5 (void) {
#if (TC_OSMUTEXNEW_5_EN)
  osMutexAttr_t attr = {NULL, 0U, NULL, 0U};
  osMutexId_t id;

  /* Call osMutexNew to create mutex object and assign a name to it */
  attr.name = "Mutex";

  id = osMutexNew (&attr);
  ASSERT_TRUE (id != NULL);

  /* Delete created mutex */
  ASSERT_TRUE (osMutexDelete(id) == osOK);
#endif
}

/*=======0=========1=========2=========3=========4=========5=========6=========7=========8=========9=========0=========1====*/
/**
\brief Test case: TC_osMutexNew_6
\details
  - Call osMutexNew to create mutex object by specifying memory for control block in attributes
*/
void TC_osMutexNew_6 (void) {
#if (TC_OSMUTEXNEW_6_EN)
  osMutexAttr_t attr = {NULL, 0U, NULL, 0U};
  osMutexId_t id;

  /* Call osMutexNew to create mutex object by specifying memory for control block in attributes */
  attr.cb_mem  = &Mutex_CbMem;
  attr.cb_size = sizeof(Mutex_CbMem);

  id = osMutexNew (&attr);
  ASSERT_TRUE (id != NULL);

  /* Delete created mutex */
  ASSERT_TRUE (osMutexDelete(id) == osOK);
#endif
}

/*=======0=========1=========2=========3=========4=========5=========6=========7=========8=========9=========0=========1====*/
/**
\brief Test case: TC_osMutexGetName_1
\details
  - Call osMutexGetName to retrieve a name of an unnamed mutex
  - Call osMutexGetName to retrieve a name of a mutex with assigned name
  - Call osMutexGetName from ISR
  - Call osMutexGetName with null object
*/
void TC_osMutexGetName_1 (void) {
#if (TC_OSMUTEXGETNAME_1_EN)
  osMutexAttr_t attr = {NULL, 0U, NULL, 0U};
  osMutexId_t id;
  char const *name = "Mutex";

  /* Create mutex object without assigned name */
  attr.name = NULL;
  id = osMutexNew (&attr);
  ASSERT_TRUE (id != NULL);

  /* Call osMutexGetName to retrieve a name of an unnamed mutex */
  ASSERT_TRUE(osMutexGetName (id) == NULL);

  /* Delete mutex object */
  ASSERT_TRUE (osMutexDelete (id) == osOK);


  /* Create mutex object with name assigned via attributes */
  attr.name = name;
  id = osMutexNew (&attr);
  ASSERT_TRUE (id != NULL);

  /* Call osMutexGetName to retrieve a name of a mutex with assigned name */
  ASSERT_TRUE (strcmp(osMutexGetName(id), name) == 0U);

  /* Call osMutexGetName from ISR */
  TST_IRQHandler = Irq_osMutexGetName_1;
  MutexId   = id;
  MutexName = name;
  SetPendingIRQ(IRQ_A);
  ASSERT_TRUE (strcmp(MutexName, name) == 0U);

  /* Delete mutex object */
  ASSERT_TRUE (osMutexDelete (id) == osOK);

  /* Call osMutexGetName with null object */
  ASSERT_TRUE (osMutexGetName (NULL) == NULL);
#endif
}

/*-----------------------------------------------------------------------------
 * TC_osMutexGetName_1: ISR handler
 *----------------------------------------------------------------------------*/
#if (TC_OSMUTEXGETNAME_1_EN)
void Irq_osMutexGetName_1 (void) {
  MutexName = osMutexGetName (MutexId);
}
#endif

/*=======0=========1=========2=========3=========4=========5=========6=========7=========8=========9=========0=========1====*/
/**
\brief Test case: TC_osMutexAcquire_1
\details
  - Call osMutexAcquire to acquire the mutex from the running thread
  - Call osMutexAcquire from ISR
  - Call osMutexAcquire with null mutex object
*/
void TC_osMutexAcquire_1 (void) {
#if (TC_OSMUTEXACQUIRE_1_EN)
  osMutexId_t id;

  /* Create a mutex object */
  id = osMutexNew (NULL);
  ASSERT_TRUE(id != NULL);

  /* Call osMutexAcquire to acquire the mutex from the running thread */
  ASSERT_TRUE (osMutexAcquire(id, osWaitForever) == osOK);

  /* Release acquired mutex */
  ASSERT_TRUE (osMutexRelease(id) == osOK);

  /* Delete the mutex */
  ASSERT_TRUE (osMutexDelete (id) == osOK);

  /* Create a mutex object */
  id = osMutexNew (NULL);
  ASSERT_TRUE(id != NULL);

  /* Call osMutexAcquire from ISR */
  TST_IRQHandler = Irq_osMutexAcquire_1;
  Isr_osStatus = osOK;
  MutexId = id;
  SetPendingIRQ(IRQ_A);
  ASSERT_TRUE (Isr_osStatus == osErrorISR);

  /* Delete the mutex */
  ASSERT_TRUE (osMutexDelete (id) == osOK);

  /* Call osMutexAcquire with null mutex object */
  ASSERT_TRUE (osMutexAcquire(NULL, 0U) == osErrorParameter);
#endif
}

/*-----------------------------------------------------------------------------
 * TC_osMutexAcquire_1: ISR handler
 *----------------------------------------------------------------------------*/
#if (TC_OSMUTEXACQUIRE_1_EN)
void Irq_osMutexAcquire_1 (void) {
  Isr_osStatus = osMutexAcquire (MutexId, 0U);
}
#endif

/*=======0=========1=========2=========3=========4=========5=========6=========7=========8=========9=========0=========1====*/
/**
\brief Test case: TC_osMutexAcquire_2
\details
  - Call osMutexAcquire without timeout and try to acquire already owned mutex
  - Call osMutexAcquire with timeout and wait to acquire already owned mutex
*/
void TC_osMutexAcquire_2 (void) {
#if (TC_OSMUTEXACQUIRE_2_EN)
  osThreadAttr_t attr = { NULL, osThreadDetached, NULL, 0U, NULL, 0U, osPriorityNone, 0U, 0U};
  osThreadId_t th_id;
  osMutexId_t id;

  /* Create a mutex object */
  id = osMutexNew (NULL);
  ASSERT_TRUE(id != NULL);

  MutexId = id;

  /* Create a thread that acquires mutex */
  attr.priority = osPriorityLow;
  th_id = osThreadNew (Th_osMutexAcquire_2, NULL, &attr);

  /* Wait for thread to execute */
  osDelay(2);

  /* Call osMutexAcquire without timeout and try to acquire already owned mutex */
  ASSERT_TRUE (osMutexAcquire(id, 0U) == osErrorResource);

  /* Call osMutexAcquire with timeout and wait to acquire already owned mutex */
  ASSERT_TRUE (osMutexAcquire(id, 5U) == osErrorTimeout);

  /* Wait for thread to release the mutex */
  osDelay(10);

  /* Check that the thread is terminated */
  ASSERT_TRUE (osThreadGetState (th_id) != osThreadBlocked);

  /* Delete the mutex */
  ASSERT_TRUE (osMutexDelete (id) == osOK);

#endif
}

/*-----------------------------------------------------------------------------
 * TC_osMutexAcquire_2: Helper thread
 *----------------------------------------------------------------------------*/
#if (TC_OSMUTEXACQUIRE_2_EN)
void Th_osMutexAcquire_2 (void *arg) {
  (void)arg;

  /* Acquire mutex */
  ASSERT_TRUE (osMutexAcquire(MutexId, 0U) == osOK);

  /* Wait ten ticks */
  osDelay(10U);

  /* Release acquired mutex */
  ASSERT_TRUE (osMutexRelease(MutexId) == osOK);

  /* Terminate self */
  osThreadTerminate(osThreadGetId());
}
#endif

/*=======0=========1=========2=========3=========4=========5=========6=========7=========8=========9=========0=========1====*/
/**
\brief Test case: TC_osMutexRelease_1
\details
  - Call osMutexRelease to release acquired mutex
  - Call osMutexRelease to release mutex that was not acquired
  - Call osMutexRelease from ISR
  - Call osMutexRelease with null mutex object
*/
void TC_osMutexRelease_1 (void) {
#if (TC_OSMUTEXRELEASE_1_EN)
  osMutexId_t id;

  /* Create a mutex object */
  id = osMutexNew (NULL);
  ASSERT_TRUE(id != NULL);

  /* Call osMutexAcquire to acquire mutex */
  ASSERT_TRUE (osMutexAcquire(id, osWaitForever) == osOK);

  /* Call osMutexRelease to release acquired mutex */
  ASSERT_TRUE (osMutexRelease(id) == osOK);

  /* Delete the mutex */
  ASSERT_TRUE (osMutexDelete (id) == osOK);


  /* Create a mutex object */
  id = osMutexNew (NULL);
  ASSERT_TRUE(id != NULL);

  /* Call osMutexRelease to release mutex that was not acquired */
  ASSERT_TRUE (osMutexRelease(id) == osErrorResource);

  /* Call osMutexAcquire to acquire mutex */
  ASSERT_TRUE (osMutexAcquire(id, osWaitForever) == osOK);

  /* Call osMutexRelease from ISR */
  TST_IRQHandler = Irq_osMutexRelease_1;
  Isr_osStatus = osOK;
  MutexId = id;
  SetPendingIRQ(IRQ_A);
  ASSERT_TRUE (Isr_osStatus == osErrorISR);

  /* Release acquired mutex */
  ASSERT_TRUE (osMutexRelease(id) == osOK);

  /* Delete the mutex */
  ASSERT_TRUE (osMutexDelete (id) == osOK);

  /* Call osMutexRelease with null mutex object */
  ASSERT_TRUE (osMutexRelease(NULL) == osErrorParameter);
#endif
}

/*-----------------------------------------------------------------------------
 * TC_osMutexRelease_1: ISR handler
 *----------------------------------------------------------------------------*/
#if (TC_OSMUTEXRELEASE_1_EN)
void Irq_osMutexRelease_1 (void) {
  Isr_osStatus = osMutexRelease (MutexId);
}
#endif

/*=======0=========1=========2=========3=========4=========5=========6=========7=========8=========9=========0=========1====*/
/**
\brief Test case: TC_osMutexGetOwner_1
\details
  - Call osMutexGetOwner when the mutex is not locked
  - Call osMutexGetOwner when the mutex is locked
  - Call osMutexGetOwner from ISR
  - Call osMutexGetOwner with null object
*/
void TC_osMutexGetOwner_1 (void) {
#if (TC_OSMUTEXGETOWNER_1_EN)
  osMutexId_t id;

  /* Create a mutex object */
  id = osMutexNew (NULL);
  ASSERT_TRUE (id != NULL);

  /* Call osMutexGetOwner when the mutex is not locked */
  ASSERT_TRUE (osMutexGetOwner (id) == NULL);

  /* Acquire mutex */
  ASSERT_TRUE (osMutexAcquire (id, 0U) == osOK);

  /* Call osMutexGetOwner when the mutex is locked */
  ASSERT_TRUE (osMutexGetOwner (id) == osThreadGetId());

  /* Call osMutexGetOwner from ISR */
  TST_IRQHandler = Irq_osMutexGetOwner_1;
  MutexId  = id;
  ThreadId = (osThreadId_t)(-1);
  SetPendingIRQ(IRQ_A);
  ASSERT_TRUE (ThreadId == NULL);

  /* Release acquired mutex */
  ASSERT_TRUE (osMutexRelease(id) == osOK);

  /* Delete mutex object */
  ASSERT_TRUE (osMutexDelete (id) == osOK);

  /* Call osMutexGetOwner with null object */
  ASSERT_TRUE (osMutexGetOwner (NULL) == NULL);
#endif
}

/*-----------------------------------------------------------------------------
 * TC_osMutexGetOwner_1: ISR handler
 *----------------------------------------------------------------------------*/
#if (TC_OSMUTEXGETOWNER_1_EN)
void Irq_osMutexGetOwner_1 (void) {
  ThreadId = osMutexGetOwner (MutexId);
}
#endif

/*=======0=========1=========2=========3=========4=========5=========6=========7=========8=========9=========0=========1====*/
/**
\brief Test case: TC_osMutexDelete_1
\details
  - Call osMutexDelete to delete a mutex
  - Call osMutexDelete from ISR
  - Call osMutexDelete with null object
*/
void TC_osMutexDelete_1 (void) {
#if (TC_OSMUTEXDELETE_1_EN)
  osMutexId_t id;

  /* Create a mutex object */
  id = osMutexNew (NULL);
  ASSERT_TRUE (id != NULL);

  /* Call osMutexDelete to delete a mutex */
  ASSERT_TRUE (osMutexDelete (id) == osOK);

  /* Create a mutex object */
  id = osMutexNew (NULL);
  ASSERT_TRUE (id != NULL);

  /* Call osMutexDelete from ISR */
  TST_IRQHandler = Irq_osMutexDelete_1;
  Isr_osStatus = osOK;
  MutexId = id;
  SetPendingIRQ(IRQ_A);
  ASSERT_TRUE (Isr_osStatus == osErrorISR);

  /* Delete the mutex */
  ASSERT_TRUE (osMutexDelete (id) == osOK);

  /* Call osMutexDelete with null object */
  ASSERT_TRUE (osMutexDelete (NULL) == osErrorParameter);
#endif
}

/*-----------------------------------------------------------------------------
 * TC_osMutexDelete_1: ISR handler
 *----------------------------------------------------------------------------*/
#if (TC_OSMUTEXDELETE_1_EN)
void Irq_osMutexDelete_1 (void) {
  Isr_osStatus = osMutexDelete (MutexId);
}
#endif

/*=======0=========1=========2=========3=========4=========5=========6=========7=========8=========9=========0=========1====*/
/**
\brief Test case: TC_MutexRobust
\details
- Test mutex robust attribute
*/
void TC_MutexRobust (void) {
#if (TC_MUTEXROBUST_EN)
  osThreadAttr_t th_attr = { NULL, osThreadDetached, NULL, 0U, NULL, 0U, osPriorityAboveNormal, 0U, 0U};
  osThreadId_t id[2];
  uint32_t cnt[2] = {0};
  osMutexAttr_t attr = {NULL, osMutexRobust, NULL, 0U};

  /* - Create and initialize a mutex object */
  MutexId = osMutexNew (&attr);
  ASSERT_TRUE (MutexId != NULL);

  if (MutexId != NULL) {
    /* Create a first thread instance that acquires the mutex */
    id[0] = osThreadNew (Th_MutexHighPrioAcq, &cnt[0], &th_attr);
    ASSERT_TRUE (id[0] != NULL);
    ASSERT_TRUE (osMutexGetOwner(MutexId) == id[0]);
    ASSERT_TRUE (cnt[0] == 1);

    /* Create a second thread instance that tries to acquire the mutex */
    id[1] = osThreadNew (Th_MutexHighPrioAcq, &cnt[1], &th_attr);
    ASSERT_TRUE (id[1] != NULL);

    /* Terminate owner thread */
    ASSERT_TRUE (osThreadTerminate (id[0]) == osOK);

    /* Check new owner */
    ASSERT_TRUE (osMutexGetOwner(MutexId) == id[1]);
    ASSERT_TRUE (cnt[1] == 1);

    /* Delete mutex object */
    ASSERT_TRUE (osMutexDelete (MutexId) == osOK);

    /* Terminate thread */
    ASSERT_TRUE (osThreadTerminate (id[1]) == osOK);
  }
#endif
}

/*=======0=========1=========2=========3=========4=========5=========6=========7=========8=========9=========0=========1====*/
/**
\brief Test case: TC_MutexPrioInherit
\details
- Test mutex prio inherit attribute
*/
void TC_MutexPrioInherit (void) {
#if (TC_MUTEXPRIOINHERIT_EN)
  osThreadAttr_t th_attr = { NULL, osThreadDetached, NULL, 0U, NULL, 0U, osPriorityAboveNormal, 0U, 0U};
  osThreadId_t id[2];
  uint32_t cnt = 0;
  osMutexAttr_t attr = {NULL, osMutexPrioInherit, NULL, 0U};

  /* Get thread id */
  id[0] = osThreadGetId();

  /* Create and initialize a mutex object */
  MutexId = osMutexNew (&attr);
  ASSERT_TRUE (MutexId != NULL);

  if (MutexId != NULL) {
    /* Acquire mutex */
    ASSERT_TRUE (osMutexAcquire (MutexId, 0) == osOK);

    /* Check this thread priority */
    ASSERT_TRUE (osThreadGetPriority (id[0]) == osPriorityNormal);

    /* Create a higher priority thread that tries to acquire the mutex */
    id[1] = osThreadNew (Th_MutexHighPrioAcq, &cnt, &th_attr);
    ASSERT_TRUE (id != NULL);

    /* Check that priority has been inherited */
    ASSERT_TRUE (osThreadGetPriority (id[0]) == osPriorityAboveNormal);
    ASSERT_TRUE (osThreadGetPriority (id[1]) == osPriorityAboveNormal);

    /* Release mutex */
    ASSERT_TRUE (osMutexRelease (MutexId) == osOK);

    /* Check that priority has been restored */
    ASSERT_TRUE (osThreadGetPriority (id[0]) == osPriorityNormal);

    /* Check that child thread runs */
    ASSERT_TRUE (cnt == 1);

    /* Terminate child thread */
    ASSERT_TRUE (osThreadTerminate (id[1]) == osOK);

    /* Delete mutex object */
    ASSERT_TRUE (osMutexDelete (MutexId) == osOK);
  }
#endif
}

/*=======0=========1=========2=========3=========4=========5=========6=========7=========8=========9=========0=========1====*/
/**
\brief Test case: TC_MutexCheckTimeout
\details
- Set time thresholds
- Create wakeup thread to acquire and release a mutex after 10 ticks
- Wait for a mutex with a defined timeout
- Check if the mutex is acquired between the minimum and maximum thresholds
- Wait for a mutex with an infinite timeout
- Check if the mutex is acquired between the minimum and maximum thresholds
*/
void TC_MutexCheckTimeout (void) {
#if (TC_MUTEXCHECKTIMEOUT_EN)
  osThreadAttr_t attr = { NULL, osThreadDetached, NULL, 0U, NULL, 0U, osPriorityAboveNormal, 0U, 0U};
  osThreadId_t id;
  osStatus_t stat;
  uint32_t t_10;

  /* Get main thread ID */
  ThreadId = osThreadGetId ();

  /* Create a semaphore object */
  MutexId = osMutexNew (NULL);
  ASSERT_TRUE (MutexId != NULL);

  if (MutexId != NULL) {
    /* Synchronize tick */
    osDelay(1U);

    /* Create wakeup thread to release a mutex after 10 ticks */
    id = osThreadNew(Th_MutexWakeup, NULL, &attr);

    if (id != NULL) {
      t_10 = osKernelGetTickCount();
      stat = osMutexAcquire (MutexId, 100);
      t_10 = osKernelGetTickCount() - t_10;

      ASSERT_TRUE (stat == osOK);
      ASSERT_TRUE (t_10 == 10U);
    }
    else {
      ASSERT_TRUE (id != NULL);
    }

    /* Wait until wakeup thread is terminated */
    osDelay(5U);

    ASSERT_TRUE (osMutexRelease (MutexId) == osOK);

    /* Create wakeup thread to release a semaphore after 10 ticks */
    id = osThreadNew(Th_MutexWakeup, NULL, &attr);

    if (id != NULL) {
      t_10 = osKernelGetTickCount();
      stat = osMutexAcquire (MutexId, osWaitForever);
      t_10 = osKernelGetTickCount() - t_10;

      ASSERT_TRUE (stat == osOK);
      ASSERT_TRUE (t_10 == 10U);
    }

    /* Wait until wakeup thread is terminated */
    osDelay(5U);

    ASSERT_TRUE (osMutexRelease (MutexId) == osOK);

    /* Delete mutex object */
    ASSERT_TRUE (osMutexDelete (MutexId)  == osOK);
  }
#endif
}

/*=======0=========1=========2=========3=========4=========5=========6=========7=========8=========9=========0=========1====*/
/**
\brief Test case: TC_MutexNestedAcquire
\details
- Create a mutex object
- Obtain a mutex object
- Create a high priority thread that waits for the same mutex
- Recursively acquire and release a mutex object
- Release a mutex
- Verify that every subsequent call released the mutex
- Delete a mutex object
- Mutex object must be released after each acquisition
*/
void TC_MutexNestedAcquire (void) {
#if (TC_MUTEXNESTEDACQUIRE_EN)
  osThreadAttr_t th_attr = { NULL, osThreadDetached, NULL, 0U, NULL, 0U, osPriorityAboveNormal, 0U, 0U};
  osMutexAttr_t attr = {NULL, osMutexRecursive, NULL, 0U};
  osStatus_t stat;

  /* - Create a mutex object */
  MutexId = osMutexNew (&attr);

  ASSERT_TRUE (MutexId != NULL);

  if (MutexId  != NULL) {
    /* - Obtain a mutex object */
    stat = osMutexAcquire (MutexId, 0);
    ASSERT_TRUE (stat == osOK);

    if (stat == osOK) {
      /* - Create a high priority thread that will wait for the same mutex */
      ThreadId = osThreadNew (Th_MutexWait, NULL, &th_attr);
      ASSERT_TRUE (ThreadId != NULL);

      /* - Recursively acquire and release a mutex object */
      RecursiveMutexAcquire (5, 5);

      /* - Release a mutex */
      stat = osMutexRelease (MutexId);
      ASSERT_TRUE (stat == osOK);
      osDelay(100);

      /* - Verify that every subsequent call released the mutex */
      ASSERT_TRUE (osMutexRelease (MutexId) == osErrorResource);
    }
    /* - Delete a mutex object */
    ASSERT_TRUE (osMutexDelete (MutexId) == osOK);
  }
#endif
}

/*=======0=========1=========2=========3=========4=========5=========6=========7=========8=========9=========0=========1====*/
/**
\brief Test case: TC_MutexPriorityInversion
\details
- Set priority of the control thread to normal
- Create low priority thread, which will acquire mutex
- Wait until low priority thread acquires mutex
- Raise priority of the control thread
- Create high priority thread, which will wait for a mutex
- Allow high priority job to wait for mutex
- Create medium priority thread
- Set priority of the control thread to be the lowest of all
- Wait until all jobs finish
- Verify thread execution order
- Thread execution order must be: Low, High, Medium
*/
void TC_MutexPriorityInversion (void) {
#if (TC_MUTEXPRIORITYINVERSION_EN)
  osThreadAttr_t th_attr = { NULL, osThreadDetached, NULL, 0U, NULL, 0U, osPriorityNone, 0U, 0U};
  osThreadId_t ctrl_id, id[3];
  osMutexAttr_t attr = {NULL, 0U, NULL, 0U};
  osStatus_t stat;
  uint32_t i;
  uint32_t flags;

  /* Init execution array */
  for (i = 0; i < 3; i++) {
    G_ExecArr[i] = 0;
  }

  /* Get id of the control thread */
  ctrl_id = osThreadGetId();

  /* - Set priority of the control thread to normal */
  stat = osThreadSetPriority (ctrl_id, osPriorityNormal);
  ASSERT_TRUE (stat == osOK);

  if (stat == osOK) {
    /* Create a mutex object */
    attr.attr_bits=osMutexPrioInherit;

    MutexId = osMutexNew (&attr);
    ASSERT_TRUE (MutexId != NULL);

    if (MutexId != NULL) {
      /* - Create low priority thread, which will acquire mutex */
      th_attr.priority = osPriorityBelowNormal;
      id[0] = osThreadNew (Th_LowPrioJob, &ctrl_id, &th_attr);
      ASSERT_TRUE (id[0] != NULL);

      if (id[0] != NULL) {
        /* - Wait until low priority thread acquires mutex */
        flags = osThreadFlagsWait (1U, 0, 100);
        ASSERT_TRUE (flags == 1U);

        if (flags == 1U) {
          /* - Raise priority of the control thread */
          stat = osThreadSetPriority (ctrl_id, osPriorityAboveNormal);
          ASSERT_TRUE (stat == osOK);

          if (stat == osOK) {
            /* - Create high priority thread, which will wait for a mutex */
            th_attr.priority = osPriorityAboveNormal;
            id[1] = osThreadNew (Th_HighPrioJob, &ctrl_id, &th_attr);
            ASSERT_TRUE (id[1] != NULL);

            if (id[1] != NULL) {
              /* - Allow high priority job to wait for mutex */
              osThreadFlagsWait (1U, 0, 100);

              /* - Create medium priority thread */
              th_attr.priority = osPriorityNormal;
              id[2] = osThreadNew (Th_MediumPrioJob, &ctrl_id, &th_attr);
              ASSERT_TRUE (id[2] != NULL);

              if (id[2] != NULL) {
                /* - Set priority of the control thread to be the lowest of all */
                stat = osThreadSetPriority (ctrl_id, osPriorityLow);
                ASSERT_TRUE (stat == osOK);

                if (stat == osOK) {
                  /* Wait until all jobs finish */
                  flags = osThreadFlagsWait (0x0EU, 0, 100);
                  ASSERT_TRUE (flags == 0x0EU);

                  if (flags == 0x0E) {
                    /* - Verify thread execution order */
                    ASSERT_TRUE (G_ExecArr[0] == 'L');
                    ASSERT_TRUE (G_ExecArr[1] == 'H');
                    ASSERT_TRUE (G_ExecArr[2] == 'M');
                  }
                }
              }
            }
          }
        }
      }
    }

    /* - Delete mutex object */
    ASSERT_TRUE (osMutexDelete (MutexId) == osOK);

    /* - Restore priority of the control thread to normal */
    stat = osThreadSetPriority (ctrl_id, osPriorityNormal);
    ASSERT_TRUE (stat == osOK);
  }
#endif
}

/*=======0=========1=========2=========3=========4=========5=========6=========7=========8=========9=========0=========1====*/
/**
\brief Test case: TC_MutexOwnership
\details
- Create a mutex object
- Create a child thread and wait until acquires mutex
- Create a child thread that tries to release a mutex
- Only thread that obtains a mutex can release it.
*/
void TC_MutexOwnership (void) {
#if (TC_MUTEXOWNERSHIP_EN)
  osThreadAttr_t attr  = { NULL, osThreadDetached, NULL, 0U, NULL, 0U, osPriorityNone, 0U, 0U};
  osThreadId_t ctrl_id, id[2];

  /* Ensure that priority of the control thread is set to normal */
  ctrl_id = osThreadGetId();
  ASSERT_TRUE (osThreadSetPriority (ctrl_id, osPriorityNormal) == osOK);

  /* - Create a mutex object */
  MutexId = osMutexNew (NULL);
  ASSERT_TRUE (MutexId != NULL);

  if (MutexId != NULL) {
    /* - Create a child thread and wait until acquires mutex */
    attr.priority = osPriorityLow;
    id[0] = osThreadNew (Th_MutexAcqLow, NULL, &attr);
    ASSERT_TRUE (id[0] != NULL);
    osDelay(10);

    if (id[0] != NULL) {
      /* - Create a child thread that trys to release a mutex */
      attr.priority = osPriorityHigh;
      id[1] = osThreadNew (Th_MutexRelHigh, NULL, &attr);
      ASSERT_TRUE (id[1] != NULL);

      /* Terminate MutexRelHigh thread */
      if (id[1] != NULL) {
        ASSERT_TRUE (osThreadTerminate (id[1]) == osOK);
      }

      /* Check ownership */
      ASSERT_TRUE (osMutexGetOwner (MutexId) == id[0]);
      /* Let MutexAcqLow thread release mutex */
      ASSERT_TRUE ((int32_t)osThreadFlagsSet(id[0], 1) >= 0);
      osDelay(10);
      /* Check ownership after releasing mutex */
      ASSERT_TRUE (osMutexGetOwner (MutexId) == NULL);

      /* Terminate MutexAcqLow thread */
      ASSERT_TRUE (osThreadTerminate (id[0]) == osOK);
    }
  }
  /* - Delete a mutex object */
  ASSERT_TRUE (osMutexDelete (MutexId) == osOK);
#endif
}

/*=======0=========1=========2=========3=========4=========5=========6=========7=========8=========9=========0=========1====*/
/**
\brief Test case: TC_MutexAllocation
\details
- Test mutex object allocation
*/
void TC_MutexAllocation (void) {
#if (TC_MUTEXALLOCATION_EN)
  osMutexId_t id[MAX_MUTEX_NUM];
  uint32_t cnt = 0U;
  uint32_t max = 0U;
  uint32_t i;

  /* Create max number of objects */
  for (i = 0U; i < MAX_MUTEX_NUM; i++) {
    id[i] = osMutexNew (NULL);

    if (id[i] == NULL) {
      max = i;
      break;
    }
  }
  ASSERT_TRUE (i > 0U);

  if (max > 0U) {
    /* Try to allocate extra object */
    ASSERT_TRUE(osMutexNew (NULL) == NULL);
  }

  osDelay(10U);

  /* Delete all */
  cnt = i;

  for (i = 0U; i < cnt; i++) {
    ASSERT_TRUE(osMutexDelete(id[i]) == osOK);
  }
#endif
}

/**
@}
*/
// end of group mutex_func
