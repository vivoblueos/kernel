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
#define MAX_SEMAPHORE_NUM  64

/* Definitions of shared variables */
#define TEST_THREAD_CNT 5
static volatile uint32_t Var_ThreadStatus[TEST_THREAD_CNT];

void Th_TestSemaphore   (void *arg);
void Th_SemaphoreWait   (void *arg);
void Th_SemaphoreWakeup (void *arg);

void Irq_osSemaphoreNew_1      (void);
void Irq_osSemaphoreGetName_1  (void);
void Irq_osSemaphoreAcquire_1  (void);
void Irq_osSemaphoreRelease_1  (void);
void Irq_osSemaphoreGetCount_1 (void);
void Irq_osSemaphoreDelete_1   (void);

/*-----------------------------------------------------------------------------
 *  Th_TestSemaphore: Semaphore access thread
 *----------------------------------------------------------------------------*/
void Th_TestSemaphore (void *arg) {
  uint32_t par = *(uint32_t *)arg;
  uint32_t sem;

  while (Var_ThreadStatus[par] == 0) {
    sem = osSemaphoreGetCount(SemaphoreId);

    if ((sem > 0) && (osSemaphoreAcquire (SemaphoreId, 0) == osOK)) {
      /* Semaphore object was acquired */
      Var_ThreadStatus[par] = 2;
    }
    else {
      /* Semaphore object is not available */
      Var_ThreadStatus[par] = 1;
    }
  }

  osThreadTerminate (osThreadGetId());
}

/*-----------------------------------------------------------------------------
 *  Th_SemaphoreWait: Semaphore wait thread
 *----------------------------------------------------------------------------*/
#if (TC_SEMAPHOREWAITTIMEOUT_EN)
void Th_SemaphoreWait (void *arg) {
  uint32_t   ticks = *((uint32_t *)arg);

  if (osSemaphoreAcquire (SemaphoreId, ticks) == osOK) {
    osThreadFlagsSet (ThreadId, 1);     /* Send signal: semaphore obtained    */
    ASSERT_TRUE (osSemaphoreRelease (SemaphoreId) == osOK);
  }
  else {
    osThreadFlagsSet (ThreadId, 0x02);     /* Send signal: semaphore not obtained*/
  }

  /* Explicitly terminate this thread */
  osThreadTerminate (osThreadGetId());
}
#endif

/*-----------------------------------------------------------------------------
 *      Wakeup thread
 *----------------------------------------------------------------------------*/
void Th_SemaphoreWakeup (void __attribute__((unused)) *arg)
{
  osDelay(10);
  /* Release semaphore to the main thread */
  ASSERT_TRUE (osSemaphoreRelease (SemaphoreId) == osOK);

  /* Explicitly terminate this thread */
  osThreadTerminate (osThreadGetId());
}

/*-----------------------------------------------------------------------------
 *      Test cases
 *----------------------------------------------------------------------------*/

/*=======0=========1=========2=========3=========4=========5=========6=========7=========8=========9=========0=========1====*/
/**
\defgroup semaphore_funcs Semaphore Functions
\brief Semaphore Functions Test Cases
\details
The test cases check the osSemaphore* functions.

@{
*/

/*=======0=========1=========2=========3=========4=========5=========6=========7=========8=========9=========0=========1====*/
/**
\brief Test case: TC_osSemaphoreNew_1
\details
  - Call osSemaphoreNew to create a binary semaphore object with initial token cleared
  - Call osSemaphoreNew to create a binary semaphore object with initial token set
  - Call osSemaphoreNew to create a counting semaphore object with initial token count cleared
  - Call osSemaphoreNew to create a counting semaphore object with initial token count set to max count={UINT8_MAX, UINT16_MAX, UINT32_MAX}
  - Call osSemaphoreNew from ISR
*/
void TC_osSemaphoreNew_1 (void) {
#if (TC_OSSEMAPHORENEW_1_EN)
  osTimerId_t id;

  /* Call osSemaphoreNew to create a binary semaphore object with initial token cleared */
  id = osSemaphoreNew (1U, 0U, NULL);
  ASSERT_TRUE (id != NULL);

  /* Delete created semaphore */
  ASSERT_TRUE (osSemaphoreDelete(id) == osOK);

  /* Call osSemaphoreNew to create a binary semaphore object with initial token set */
  id = osSemaphoreNew (1U, 1U, NULL);
  ASSERT_TRUE (id != NULL);

  /* Delete created semaphore */
  ASSERT_TRUE (osSemaphoreDelete(id) == osOK);

  /* Call osSemaphoreNew to create a counting semaphore object with initial token count cleared */
  id = osSemaphoreNew (UINT8_MAX, 0U, NULL);
  ASSERT_TRUE (id != NULL);

  /* Delete created semaphore */
  ASSERT_TRUE (osSemaphoreDelete(id) == osOK);

  /* Call osSemaphoreNew to create a counting semaphore object with initial token count set to max count={UINT8_MAX, UINT16_MAX, UINT32_MAX} */
  id = osSemaphoreNew (UINT8_MAX, UINT8_MAX, NULL);
  ASSERT_TRUE (id != NULL);

  /* Delete created semaphore */
  ASSERT_TRUE (osSemaphoreDelete(id) == osOK);

  id = osSemaphoreNew (UINT16_MAX, UINT16_MAX, NULL);
  ASSERT_TRUE (id != NULL);

  /* Delete created semaphore */
  ASSERT_TRUE (osSemaphoreDelete(id) == osOK);

  id = osSemaphoreNew (MAX_SEMAPHORE_TOKEN_CNT, MAX_SEMAPHORE_TOKEN_CNT, NULL);
  ASSERT_TRUE (id != NULL);

  /* Delete created semaphore */
  ASSERT_TRUE (osSemaphoreDelete(id) == osOK);

  /* Call osSemaphoreNew from ISR */
  TST_IRQHandler = Irq_osSemaphoreNew_1;
  SemaphoreId = (osSemaphoreId_t)(-1);
  SetPendingIRQ(IRQ_A);
  ASSERT_TRUE (SemaphoreId == NULL);
#endif
}

/*-----------------------------------------------------------------------------
 * TC_osSemaphoreNew_1: ISR handler
 *----------------------------------------------------------------------------*/
#if (TC_OSSEMAPHORENEW_1_EN)
void Irq_osSemaphoreNew_1 (void) {
  SemaphoreId = osSemaphoreNew (1U, 1U, NULL);
}
#endif

/*=======0=========1=========2=========3=========4=========5=========6=========7=========8=========9=========0=========1====*/
/**
\brief Test case: TC_osSemaphoreNew_2
\details
  - Call osSemaphoreNew to create semaphore object and assign a name to it
*/
void TC_osSemaphoreNew_2 (void) {
#if (TC_OSSEMAPHORENEW_2_EN)
  osSemaphoreAttr_t attr = {NULL, 0U, NULL, 0U};
  osSemaphoreId_t id;

  /* Call osSemaphoreNew to create semaphore object and assign a name to it */
  attr.name = "Semaphore";

  id = osSemaphoreNew (1U, 0U, &attr);
  ASSERT_TRUE (id != NULL);

  /* Delete created semaphore */
  ASSERT_TRUE (osSemaphoreDelete(id) == osOK);
#endif
}

/*=======0=========1=========2=========3=========4=========5=========6=========7=========8=========9=========0=========1====*/
/**
\brief Test case: TC_osSemaphoreNew_3
\details
  - Call osSemaphoreNew to create semaphore object by specifying memory for control block in attributes
*/
void TC_osSemaphoreNew_3 (void) {
#if (TC_OSSEMAPHORENEW_3_EN)
  osSemaphoreAttr_t attr = {NULL, 0U, NULL, 0U};
  osSemaphoreId_t id;

  /* Call osSemaphoreNew to create semaphore object by specifying memory for control block in attributes */
  attr.cb_mem  = &Semaphore_CbMem;
  attr.cb_size = sizeof(Semaphore_CbMem);

  id = osSemaphoreNew (1U, 0U, &attr);
  ASSERT_TRUE (id != NULL);

  /* Delete created semaphore */
  ASSERT_TRUE (osSemaphoreDelete(id) == osOK);
#endif
}

/*=======0=========1=========2=========3=========4=========5=========6=========7=========8=========9=========0=========1====*/
/**
\brief Test case: TC_osSemaphoreGetName_1
\details
  - Call osSemaphoreGetName to retrieve a name of an unnamed semaphore
  - Call osSemaphoreGetName to retrieve a name of a semaphore with assigned name
  - Call osSemaphoreGetName from ISR
  - Call osSemaphoreGetName with null object
*/
void TC_osSemaphoreGetName_1 (void) {
#if (TC_OSSEMAPHOREGETNAME_1_EN)
  osSemaphoreAttr_t attr = {NULL, 0U, NULL, 0U};
  osSemaphoreId_t id;
  char const *name = "Semaphore";

  /* Create semaphore object without assigned name */
  attr.name = NULL;
  id = osSemaphoreNew (1U, 1U, &attr);
  ASSERT_TRUE (id != NULL);

  /* Call osSemaphoreGetName to retrieve a name of an unnamed semaphore */
  ASSERT_TRUE(osSemaphoreGetName (id) == NULL);

  /* Delete semaphore object */
  ASSERT_TRUE (osSemaphoreDelete (id) == osOK);


  /* Create semaphore object with name assigned via attributes */
  attr.name = name;
  id = osSemaphoreNew (1U, 1U, &attr);
  ASSERT_TRUE (id != NULL);

  /* Call osSemaphoreGetName to retrieve a name of a semaphore with assigned name */
  ASSERT_TRUE (strcmp(osSemaphoreGetName(id), name) == 0U);

  /* Call osSemaphoreGetName from ISR */
  TST_IRQHandler = Irq_osSemaphoreGetName_1;
  SemaphoreId   = id;
  SemaphoreName = name;
  SetPendingIRQ(IRQ_A);
  ASSERT_TRUE (strcmp(SemaphoreName, name) == 0U);

  /* Delete semaphore object */
  ASSERT_TRUE (osSemaphoreDelete (id) == osOK);

  /* Call osSemaphoreGetName with null object */
  ASSERT_TRUE (osSemaphoreGetName (NULL) == NULL);
#endif
}

/*-----------------------------------------------------------------------------
 * TC_osSemaphoreGetName_1: ISR handler
 *----------------------------------------------------------------------------*/
#if (TC_OSSEMAPHOREGETNAME_1_EN)
void Irq_osSemaphoreGetName_1 (void) {
  SemaphoreName = osSemaphoreGetName (SemaphoreId);
}
#endif

/*=======0=========1=========2=========3=========4=========5=========6=========7=========8=========9=========0=========1====*/
/**
\brief Test case: TC_osSemaphoreAcquire_1
\details
  - Call osSemaphoreAcquire to acquire binary semaphore
  - Call osSemaphoreAcquire to acquire counting semaphore
  - Call osSemaphoreAcquire from ISR (non-zero timeout)
  - Call osSemaphoreAcquire with null semaphore object
*/
void TC_osSemaphoreAcquire_1 (void) {
#if (TC_OSSEMAPHOREACQUIRE_1_EN)
  osSemaphoreId_t id;

  /* Create a semaphore object */
  id = osSemaphoreNew (1U, 1U, NULL);
  ASSERT_TRUE(id != NULL);

  /* Call osSemaphoreAcquire to acquire binary semaphore */
  ASSERT_TRUE (osSemaphoreAcquire(id, osWaitForever) == osOK);

  /* Delete the semaphore */
  ASSERT_TRUE (osSemaphoreDelete (id) == osOK);


  /* Create a semaphore object */
  id = osSemaphoreNew (5U, 5U, NULL);
  ASSERT_TRUE(id != NULL);

  /* Call osSemaphoreAcquire to acquire counting semaphore */
  ASSERT_TRUE (osSemaphoreAcquire(id, osWaitForever) == osOK);

  /* Delete the semaphore */
  ASSERT_TRUE (osSemaphoreDelete (id) == osOK);


  /* Create a semaphore object */
  id = osSemaphoreNew (1U, 1U, NULL);
  ASSERT_TRUE(id != NULL);

  /* Call osSemaphoreAcquire from ISR (non-zero timeout) */
  TST_IRQHandler = Irq_osSemaphoreAcquire_1;
  Isr_osStatus = osOK;
  SemaphoreId = id;
  SetPendingIRQ(IRQ_A);
  ASSERT_TRUE (Isr_osStatus == osErrorParameter);

  /* Delete the semaphore */
  ASSERT_TRUE (osSemaphoreDelete (id) == osOK);

  /* Call osSemaphoreAcquire with null semaphore object */
  ASSERT_TRUE (osSemaphoreAcquire(NULL, 0U) == osErrorParameter);
#endif
}

/*-----------------------------------------------------------------------------
 * TC_osSemaphoreAcquire_1: ISR handler
 *----------------------------------------------------------------------------*/
#if (TC_OSSEMAPHOREACQUIRE_1_EN)
void Irq_osSemaphoreAcquire_1 (void) {
  Isr_osStatus = osSemaphoreAcquire (SemaphoreId, osWaitForever);
}
#endif

/*=======0=========1=========2=========3=========4=========5=========6=========7=========8=========9=========0=========1====*/
/**
\brief Test case: TC_osSemaphoreRelease_1
\details
  - Call osSemaphoreRelease to release acquired binary semaphore
  - Call osSemaphoreRelease to release acquired counting semaphore
  - Call osSemaphoreRelease to release binary semaphore that was not acquired
  - Call osSemaphoreRelease to release counting semaphore that was not acquired
  - Call osSemaphoreRelease from ISR
  - Call osSemaphoreRelease with null semaphore object
*/
void TC_osSemaphoreRelease_1 (void) {
#if (TC_OSSEMAPHORERELEASE_1_EN)
  osSemaphoreId_t id;

  /* Create a semaphore object */
  id = osSemaphoreNew (1U, 1U, NULL);
  ASSERT_TRUE(id != NULL);

  /* Call osSemaphoreAcquire to acquire semaphore */
  ASSERT_TRUE (osSemaphoreAcquire(id, osWaitForever) == osOK);

  /* Call osSemaphoreRelease to release acquired binary semaphore */
  ASSERT_TRUE (osSemaphoreRelease(id) == osOK);

  /* Delete the semaphore */
  osSemaphoreDelete (id);


  /* Create a semaphore object */
  id = osSemaphoreNew (5U, 5U, NULL);
  ASSERT_TRUE(id != NULL);

  /* Call osSemaphoreAcquire to acquire semaphore */
  ASSERT_TRUE (osSemaphoreAcquire(id, osWaitForever) == osOK);

  /* Call osSemaphoreRelease to release acquired counting semaphore */
  ASSERT_TRUE (osSemaphoreRelease(id) == osOK);

  /* Delete the semaphore */
  osSemaphoreDelete (id);


  /* Create a semaphore object */
  id = osSemaphoreNew (1U, 1U, NULL);
  ASSERT_TRUE(id != NULL);

  /* Call osSemaphoreRelease to release binary semaphore that was not acquired */
  ASSERT_TRUE (osSemaphoreRelease(id) == osErrorResource);

  /* Delete the semaphore */
  osSemaphoreDelete (id);


  /* Create a semaphore object */
  id = osSemaphoreNew (5U, 5U, NULL);
  ASSERT_TRUE(id != NULL);

  /* Call osSemaphoreRelease to release counting semaphore that was not acquired */
  ASSERT_TRUE (osSemaphoreRelease(id) == osErrorResource);

  /* Delete the semaphore */
  osSemaphoreDelete (id);


  /* Create a semaphore object */
  id = osSemaphoreNew (5U, 5U, NULL);
  ASSERT_TRUE(id != NULL);

  /* Call osSemaphoreAcquire to acquire semaphore */
  ASSERT_TRUE (osSemaphoreAcquire(id, osWaitForever) == osOK);

  /* Call osSemaphoreRelease from ISR */
  TST_IRQHandler = Irq_osSemaphoreRelease_1;
  Isr_osStatus = osError;
  SemaphoreId = id;
  SetPendingIRQ(IRQ_A);
  ASSERT_TRUE (Isr_osStatus == osOK);

  /* Delete the semaphore */
  ASSERT_TRUE (osSemaphoreDelete (id) == osOK);

  /* Call osSemaphoreRelease with null semaphore object */
  ASSERT_TRUE (osSemaphoreRelease(NULL) == osErrorParameter);
#endif
}

/*-----------------------------------------------------------------------------
 * TC_osSemaphoreRelease_1: ISR handler
 *----------------------------------------------------------------------------*/
#if (TC_OSSEMAPHORERELEASE_1_EN)
void Irq_osSemaphoreRelease_1 (void) {
  Isr_osStatus = osSemaphoreRelease (SemaphoreId);
}
#endif

/*=======0=========1=========2=========3=========4=========5=========6=========7=========8=========9=========0=========1====*/
/**
\brief Test case: TC_osSemaphoreGetCount_1
\details
  - Call osSemaphoreGetCount to get token count of an initialized semaphore
  - Call osSemaphoreGetCount to get token count of an acquired semaphore
  - Call osSemaphoreGetCount from ISR
  - Call osSemaphoreGetCount with a null object id
*/
void TC_osSemaphoreGetCount_1 (void) {
#if (TC_OSSEMAPHOREGETCOUNT_1_EN)
  osSemaphoreId_t id;
  uint32_t i;

  /* Create a semaphore object */
  id = osSemaphoreNew (MAX_SEMAPHORE_TOKEN_CNT, MAX_SEMAPHORE_TOKEN_CNT, NULL);
  ASSERT_TRUE (id != NULL);

  /* Call osSemaphoreGetCount to get token count of an initialized semaphore */
  ASSERT_TRUE (osSemaphoreGetCount (id) == MAX_SEMAPHORE_TOKEN_CNT);

  /* Acquire all tokens */
  for (i = 1U; i <= MAX_SEMAPHORE_TOKEN_CNT; i++) {
    ASSERT_TRUE (osSemaphoreAcquire (id, 0U) == osOK);

    /* Call osSemaphoreGetCount to get token count of an acquired semaphore */
    ASSERT_TRUE (osSemaphoreGetCount (id) == (MAX_SEMAPHORE_TOKEN_CNT-i));
  }

  /* Release all tokens */
  for (i = 0U; i < MAX_SEMAPHORE_TOKEN_CNT; i++) {
    osSemaphoreRelease (id);
  }

  /* Call osSemaphoreGetCount from ISR */
  TST_IRQHandler = Irq_osSemaphoreGetCount_1;
  SemaphoreId = id;
  Isr_u32 = 0U;
  SetPendingIRQ(IRQ_A);
  ASSERT_TRUE (Isr_u32 == MAX_SEMAPHORE_TOKEN_CNT);

  /* Delete the semaphore */
  ASSERT_TRUE (osSemaphoreDelete (id) == osOK);

  /* Call osSemaphoreGetCount with a null object id */
  ASSERT_TRUE (osSemaphoreGetCount (NULL) == 0U);
#endif
}

/*-----------------------------------------------------------------------------
 * TC_osSemaphoreGetCount_1: ISR handler
 *----------------------------------------------------------------------------*/
#if (TC_OSSEMAPHOREGETCOUNT_1_EN)
void Irq_osSemaphoreGetCount_1 (void) {
  Isr_u32 = osSemaphoreGetCount (SemaphoreId);
}
#endif

/*=======0=========1=========2=========3=========4=========5=========6=========7=========8=========9=========0=========1====*/
/**
\brief Test case: TC_osSemaphoreDelete_1
\details
  - Call osSemaphoreDelete to delete a semaphore
  - Call osSemaphoreDelete from ISR
  - Call osSemaphoreDelete with null object
*/
void TC_osSemaphoreDelete_1 (void) {
#if (TC_OSSEMAPHOREDELETE_1_EN)
  osSemaphoreId_t id;

  /* Create a semaphore object */
  id = osSemaphoreNew (1U, 1U, NULL);
  ASSERT_TRUE (id != NULL);

  /* Call osSemaphoreDelete to delete a semaphore */
  ASSERT_TRUE (osSemaphoreDelete (id) == osOK);

  /* Create a semaphore object */
  id = osSemaphoreNew (1U, 1U, NULL);
  ASSERT_TRUE (id != NULL);

  /* Call osSemaphoreDelete from ISR */
  TST_IRQHandler = Irq_osSemaphoreDelete_1;
  Isr_osStatus = osOK;
  SemaphoreId = id;
  SetPendingIRQ(IRQ_A);
  ASSERT_TRUE (Isr_osStatus == osErrorISR);

  /* Delete the semaphore */
  osSemaphoreDelete (id);

  /* Call osSemaphoreDelete with null object */
  ASSERT_TRUE (osSemaphoreDelete (NULL) == osErrorParameter);
#endif
}

/*-----------------------------------------------------------------------------
 * TC_osSemaphoreDelete_1: ISR handler
 *----------------------------------------------------------------------------*/
#if (TC_OSSEMAPHOREDELETE_1_EN)
void Irq_osSemaphoreDelete_1 (void) {
  Isr_osStatus = osSemaphoreDelete (SemaphoreId);
}
#endif

/*=======0=========1=========2=========3=========4=========5=========6=========7=========8=========9=========0=========1====*/
/**
\brief Test case: TC_SemaphoreCreateAndDelete
\details
- Create a semaphore with initial count parameter equal to zero
- Delete created semaphore object
- Create a semaphore with initial count parameter equal to MAX_SEMAPHORE_TOKEN_CNT
- Delete created semaphore object
*/
void TC_SemaphoreCreateAndDelete (void) {
#if (TC_SEMAPHORECREATEANDDELETE_EN)
  osSemaphoreId_t  id;

  /* - Create a semaphore with initial count parameter equal to zero */
  id = osSemaphoreNew (1, 0, NULL);
  ASSERT_TRUE (id != NULL);

  if (id != NULL) {
    /* - Delete created semaphore object */
    ASSERT_TRUE (osSemaphoreDelete (id) == osOK);
  }

  /* - Create a semaphore with initial count parameter equal to osFeature_Semaphore */
  id = osSemaphoreNew (MAX_SEMAPHORE_TOKEN_CNT, MAX_SEMAPHORE_TOKEN_CNT, NULL);
  ASSERT_TRUE (id != NULL);

  if (id != NULL) {
    /* - Delete created semaphore object */
    ASSERT_TRUE (osSemaphoreDelete (id) == osOK);
  }
#endif
}

/*=======0=========1=========2=========3=========4=========5=========6=========7=========8=========9=========0=========1====*/
/**
\brief Test case: TC_SemaphoreObtainCounting
\details
- Create a counting semaphore object
- Obtain all available tokens
- Verify that all available tokens are obtained
- Release all tokens
- Delete a counting semaphore object
*/
void TC_SemaphoreObtainCounting (void) {
#if (TC_SEMAPHOREOBTAINCOUNTING_EN)
  osSemaphoreId_t id;
  uint32_t cnt;

  /* - Create a counting semaphore object */
  id = osSemaphoreNew (MAX_SEMAPHORE_TOKEN_CNT, MAX_SEMAPHORE_TOKEN_CNT, NULL);
  ASSERT_TRUE (id != NULL);

  if (id != NULL) {
    /* - Obtain all available tokens */
    for (cnt = 0; cnt < MAX_SEMAPHORE_TOKEN_CNT; cnt++) {
      ASSERT_TRUE (osSemaphoreAcquire (id, 0) == osOK);
    }
    /* - Verify that all available tokens are obtained */
    ASSERT_TRUE (osSemaphoreAcquire (id, 10) == osErrorTimeout);
    ASSERT_TRUE (osSemaphoreAcquire (id, 0) == osErrorResource);

    /* - Release all tokens */
    for (cnt = 0; cnt < MAX_SEMAPHORE_TOKEN_CNT; cnt++) {
      ASSERT_TRUE (osSemaphoreRelease (id) == osOK);
    }
    /* All tokens have been released, check return value */
    ASSERT_TRUE (osSemaphoreRelease (id) == osErrorResource);

    /* - Delete a counting semaphore object */
    ASSERT_TRUE (osSemaphoreDelete (id) == osOK);
  }

  /* - Create a counting semaphore object with one token*/
  id = osSemaphoreNew (1, 1, NULL);
  ASSERT_TRUE (id != NULL);

  if (id != NULL) {
    /* - Obtain the available token */
    ASSERT_TRUE (osSemaphoreAcquire (id, 0) == osOK);

    /* - Verify that the token is obtained */
    ASSERT_TRUE (osSemaphoreAcquire (id, 10) == osErrorTimeout);
    ASSERT_TRUE (osSemaphoreAcquire (id, 0) == osErrorResource);

    /* - Release token */
    ASSERT_TRUE (osSemaphoreRelease (id) == osOK);

    /* - Token has been released, check return value */
    ASSERT_TRUE (osSemaphoreRelease (id) == osErrorResource);

    /* - Delete a counting semaphore object */
    ASSERT_TRUE (osSemaphoreDelete (id) == osOK);
  }
#endif
}

/*=======0=========1=========2=========3=========4=========5=========6=========7=========8=========9=========0=========1====*/
/**
\brief Test case: TC_SemaphoreObtainBinary
\details
- Create a binary semaphore object
- Obtain available token
- Verify that there is no available tokens left
- Release obtained token
- Verify that no more tokens can be released
- Delete a binary semaphore object
*/
void TC_SemaphoreObtainBinary (void) {
#if (TC_SEMAPHOREOBTAINBINARY_EN)
  osSemaphoreId_t id;
  uint32_t avail;

  /* - Create a binary semaphore */
  id = osSemaphoreNew (1, 1, NULL);
  ASSERT_TRUE (id != NULL);

  if (id != NULL) {
    /* - Obtain available token */
    avail = osSemaphoreGetCount (id);
    ASSERT_TRUE (avail == 1);

    if (avail == 1) {
      /* - Acquire */
      ASSERT_TRUE (osSemaphoreAcquire (id,  0) == osOK);
      /* - Verify that there is no available tokens left */
      ASSERT_TRUE (osSemaphoreAcquire (id,  0) == osErrorResource);
      ASSERT_TRUE (osSemaphoreAcquire (id, 10) == osErrorTimeout);
      /* - Release obtained token */
      ASSERT_TRUE (osSemaphoreRelease (id) == osOK);
    }
    /* - Delete a binary semaphore object */
    ASSERT_TRUE (osSemaphoreDelete  (id) == osOK);
  }
#endif
}

/*=======0=========1=========2=========3=========4=========5=========6=========7=========8=========9=========0=========1====*/
/**
\brief Test case: TC_SemaphoreWaitForBinary
\details
- Create a binary semaphore
- Create multiple instances of a test thread that obtains semaphore
- Wait until thread instances finish
- Check if semaphore was acquired
- Check if only one thread got semaphore object
- Release and delete a semaphore
- Only one thread instance must acquire semaphore object
*/
void TC_SemaphoreWaitForBinary (void) {
#if (TC_SEMAPHOREWAITFORBINARY_EN)
  osThreadAttr_t attr = { NULL, osThreadDetached, NULL, 0U, NULL, 0U, osPriorityNormal, 0U, 0U};
  uint32_t par[] = {0, 1, 2};
  uint32_t i, j;

  /* Clear thread status array */
  for (i = 0; i < 3; i++) {
    Var_ThreadStatus[i] = 0;
  }

  /* - Create a binary semaphore */
  SemaphoreId = osSemaphoreNew (1, 1, NULL);
  ASSERT_TRUE (SemaphoreId != NULL);

  if (SemaphoreId != NULL) {
    /* Synchronize to the time slice */
    osDelay (1);

    /* - Create multiple instances of a test thread that obtains semaphore */
    osThreadNew (Th_TestSemaphore, &par[0], &attr);
    osThreadNew (Th_TestSemaphore, &par[1], &attr);
    osThreadNew (Th_TestSemaphore, &par[2], &attr);

    /* - Wait until thread instances finish */
    osDelay (50);

    /* - Check if semaphore was acquired */
    j = 0xFF;
    for (i = 0; i < 3; i++) {
      if (Var_ThreadStatus[i] == 2) j = i;
    }
    ASSERT_TRUE (j != 0xFF);            /* Ensure semaphore was acquired      */

    /* - Check if only one thread got semaphore object */
    for (i = 0; i < 3; i++) {
      if (i != j) {
        ASSERT_TRUE (Var_ThreadStatus[i] == 1);
      }
    }

    /* - Release and delete a semaphore */
    ASSERT_TRUE (osSemaphoreRelease (SemaphoreId) == osOK);
    ASSERT_TRUE (osSemaphoreDelete  (SemaphoreId) == osOK);
  }
#endif
}

/*=======0=========1=========2=========3=========4=========5=========6=========7=========8=========9=========0=========1====*/
/**
\brief Test case: TC_SemaphoreWaitForCounting
\details
- Create semaphore with index count parameter equal to 3
- Create multiple instances of a test thread that acquires semaphore
- Wait until thread instances finish
- Check if only available resources were acquired
- Release and delete a semaphore object
- Only one thread instance must acquire semaphore object
*/
void TC_SemaphoreWaitForCounting (void) {
#if (TC_SEMAPHOREWAITFORCOUNTING_EN)
  osThreadAttr_t attr = { NULL, osThreadDetached, NULL, 0U, NULL, 0U, osPriorityNormal, 0U, 0U};
  uint32_t par[] = {0, 1, 2, 3, 4};
  uint32_t i, acq, notacq;

  /* Clear thread status array */
  for (i = 0; i < 5; i++) {
    Var_ThreadStatus[i] = 0;
  }

  /* - Create semaphore */
  SemaphoreId = osSemaphoreNew (3, 3, NULL);
  ASSERT_TRUE (SemaphoreId != NULL);

  if (SemaphoreId != NULL) {
    /* Synchronize to the time slice */
    osDelay (1);

    /* - Create multiple instances of a test thread */
    osThreadNew (Th_TestSemaphore, &par[0], &attr);
    osThreadNew (Th_TestSemaphore, &par[1], &attr);
    osThreadNew (Th_TestSemaphore, &par[2], &attr);
    osThreadNew (Th_TestSemaphore, &par[3], &attr);
    osThreadNew (Th_TestSemaphore, &par[4], &attr);

    /* - Wait until thread instances finish */
    osDelay (100);

    /* - Check if only available resources were acquired */
    acq    = 0;
    notacq = 0;
    for (i = 0; i < 5; i++) {
      if (Var_ThreadStatus[i] == 2) acq++;
      if (Var_ThreadStatus[i] == 1) notacq++;
    }
    ASSERT_TRUE (acq    == 3);          /* Ensure available resources were acquired */
    ASSERT_TRUE (notacq == 2);

    /* - Release and delete a semaphore object */
    ASSERT_TRUE (osSemaphoreRelease (SemaphoreId) == osOK);
    ASSERT_TRUE (osSemaphoreDelete  (SemaphoreId) == osOK);
  }
#endif
}

/*=======0=========1=========2=========3=========4=========5=========6=========7=========8=========9=========0=========1====*/
/**
\brief Test case: TC_SemaphoreZeroCount
\details
- Create a semaphore with initial count zero
- Try to obtain a semaphore token
- Try to release a semaphore token
- Delete a semaphore object
*/
void TC_SemaphoreZeroCount (void) {
#if (TC_SEMAPHOREZEROCOUNT_EN)
  osSemaphoreId_t id;

  /* - Create a semaphore with initial count zero */
  id = osSemaphoreNew (1, 0, NULL);
  ASSERT_TRUE (id != NULL);

  if (id != NULL) {
    /* - Try to obtain a semaphore token */
    ASSERT_TRUE (osSemaphoreAcquire (id, 0) == osErrorResource);
    /* - Try to release a semaphore token */
    ASSERT_TRUE (osSemaphoreRelease (id) == osOK);
    /* - Delete a semaphore object */
    ASSERT_TRUE (osSemaphoreDelete  (id) == osOK);
  }
#endif
}

/*=======0=========1=========2=========3=========4=========5=========6=========7=========8=========9=========0=========1====*/
/**
\brief Test case: TC_SemaphoreWaitTimeout
\details
- Obtain a semaphore object
- Create a thread that waits for a semaphore
- Delay parent thread to allow child thread wait for semaphore
- Check if child thread was able to obtain a semaphore or not
*/
void TC_SemaphoreWaitTimeout (void) {
#if (TC_SEMAPHOREWAITTIMEOUT_EN)
  osThreadAttr_t attr = { NULL, osThreadDetached, NULL, 0U, NULL, 0U, osPriorityBelowNormal, 0U, 0U};
  uint32_t wait_ticks;
  uint32_t flags;

  ThreadId = osThreadGetId ();

  /* Create a semaphore object */
  SemaphoreId = osSemaphoreNew (1, 1, NULL);
  ASSERT_TRUE (SemaphoreId != NULL);

  if (SemaphoreId != NULL) {
    /* - Obtain a semaphore object */
    ASSERT_TRUE (osSemaphoreAcquire (SemaphoreId, 0) == osOK);

    /* Clear signals */
    osThreadFlagsClear (0x03U);

    /* Synchronize to the time slice */
    osDelay (1);

    /* - Create a child thread that waits for a semaphore */
    wait_ticks = 10;
    ASSERT_TRUE (osThreadNew (Th_SemaphoreWait, &wait_ticks, &attr) != NULL);

    /* - Delay parent thread to allow child thread wait for semaphore */
    osDelay (9);

    /* - Check if child thread was able to obtain a semaphore or not */
    flags = osThreadFlagsWait (1U, 0, 0);
    ASSERT_TRUE (flags == (uint32_t)osErrorResource);

    /* Wait for child thread to set a signal */
    osDelay (3);
    flags = osThreadFlagsWait (0x02U, 0, 0);
    ASSERT_TRUE (flags == 0x02U);

    /* Delete a semaphore object */
    ASSERT_TRUE (osSemaphoreDelete (SemaphoreId) == osOK);
  }

  /* Restore priority of the main thread back to normal */
  ASSERT_TRUE (osThreadSetPriority (ThreadId, osPriorityNormal) == osOK);
#endif
}


/*=======0=========1=========2=========3=========4=========5=========6=========7=========8=========9=========0=========1====*/
/**
\brief Test case: TC_SemaphoreCheckTimeout
\details
- Set time thresholds
- Create wakeup thread to release a semaphore after 10 ticks
- Wait for a semaphore with a defined timeout
- Check if the semaphore is acquired between the minimum and maximum thresholds
- Wait for a semaphore with an infinite timeout
- Check if the semaphore is acquired between the minimum and maximum thresholds
*/
void TC_SemaphoreCheckTimeout (void) {
#if (TC_SEMAPHORECHECKTIMEOUT_EN)
  osThreadAttr_t attr = { NULL, osThreadDetached, NULL, 0U, NULL, 0U, osPriorityBelowNormal, 0U, 0U};
  osThreadId_t id;
  osStatus_t stat;
  uint32_t t_10;

  /* Get main thread ID */
  ThreadId = osThreadGetId ();

  /* Create a semaphore object */
  SemaphoreId = osSemaphoreNew (1, 0, NULL);
  ASSERT_TRUE (SemaphoreId != NULL);

  if (SemaphoreId != NULL) {
    /* Synchronize tick */
    osDelay(1U);

    /* Create wakeup thread to release a semaphore after 10 ticks */
    id = osThreadNew(Th_SemaphoreWakeup, NULL, &attr);

    if (id != NULL) {
      t_10 = osKernelGetTickCount();
      stat = osSemaphoreAcquire (SemaphoreId, 100);
      t_10 = osKernelGetTickCount() - t_10;

      ASSERT_TRUE (stat == osOK);
      ASSERT_TRUE (t_10 == 10U);
    }
    else {
      ASSERT_TRUE (id != NULL);
    }

    /* Wait until wakeup thread is terminated */
    osDelay(5U);

    /* Create wakeup thread to release a semaphore after 10 ticks */
    id = osThreadNew(Th_SemaphoreWakeup, NULL, &attr);

    if (id != NULL) {
      t_10 = osKernelGetTickCount();
      stat = osSemaphoreAcquire (SemaphoreId, osWaitForever);
      t_10 = osKernelGetTickCount() - t_10;

      ASSERT_TRUE (stat == osOK);
      ASSERT_TRUE (t_10 == 10U);
    }
    else {
      ASSERT_TRUE (id != NULL);
    }

    /* Wait until wakeup thread is terminated */
    osDelay(5U);

    /* Delete a semaphore object */
    ASSERT_TRUE (osSemaphoreDelete (SemaphoreId) == osOK);
  }
#endif
}

/*=======0=========1=========2=========3=========4=========5=========6=========7=========8=========9=========0=========1====*/
/**
\brief Test case: TC_SemaphoreAllocation
\details
- Test semaphore object allocation
*/
void TC_SemaphoreAllocation (void) {
#if (TC_SEMAPHOREALLOCATION_EN)
  osSemaphoreId_t id[MAX_SEMAPHORE_NUM];
  uint32_t cnt = 0U;
  uint32_t max = 0U;
  uint32_t i;

  /* Create max number of objects */
  for (i = 0U; i < MAX_SEMAPHORE_NUM; i++) {
    id[i] = osSemaphoreNew (1U, 1U, NULL);

    if (id[i] == NULL) {
      max = i;
      break;
    }
  }
  ASSERT_TRUE (i > 0U);

  if (max > 0U) {
    /* Try to allocate extra object */
    ASSERT_TRUE(osSemaphoreNew (1U, 1U, NULL) == NULL);
  }

  osDelay(10);

  /* Delete all */
  cnt = i;

  for (i = 0U; i < cnt; i++) {
    ASSERT_TRUE(osSemaphoreDelete(id[i]) == osOK);
  }
#endif
}


/**
@}
*/
// end of group semaphore_funcs
