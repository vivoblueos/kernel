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
#define MAX_MSGQUEUE_NUM  64

#define MSGQ_SZ   4
#define MSGQ_CNT 16

static uint8_t MsgWaitCnt;

void Th_MsgQWait   (void *arg);
void Th_MsgQWakeup (void *arg);

void Irq_osMessageQueueNew_1         (void);
void Irq_osMessageQueueGetName_1     (void);
void Irq_osMessageQueuePut_1         (void);
void Irq_osMessageQueuePut_2         (void);
void Irq_osMessageQueueGet_1         (void);
void Irq_osMessageQueueGet_2         (void);
void Irq_osMessageQueueGetCapacity_1 (void);
void Irq_osMessageQueueGetMsgSize_1  (void);
void Irq_osMessageQueueGetCount_1    (void);
void Irq_osMessageQueueGetSpace_1    (void);
void Irq_osMessageQueueReset_1       (void);
void Irq_osMessageQueueDelete_1      (void);
void Irq_MsgFromThreadToISR          (void);
void Irq_MsgFromISRToThread          (void);

/*-----------------------------------------------------------------------------
 *      Test cases
 *----------------------------------------------------------------------------*/

/*=======0=========1=========2=========3=========4=========5=========6=========7=========8=========9=========0=========1====*/
/**
\defgroup msgqueue_funcs Message Queue Functions
\brief Message Queue Functions Test Cases
\details
The test cases check the osMessage* functions.

@{
*/

/*=======0=========1=========2=========3=========4=========5=========6=========7=========8=========9=========0=========1====*/
/**
\brief Test case: TC_osMessageQueueNew_1
\details
  - Call osMessageQueueNew to create a message queue object
  - Call osMessageQueueNew from ISR
*/
void TC_osMessageQueueNew_1 (void) {
#if (TC_OSMESSAGEQUEUENEW_1_EN)
  osMessageQueueId_t id;

  /* Call osMessageQueueNew to create a message queue object */
  id = osMessageQueueNew (1U, 4U, NULL);
  ASSERT_TRUE (id != NULL);

  /* Delete created message queue */
  ASSERT_TRUE (osMessageQueueDelete(id) == osOK);

  /* Call osMessageQueueNew from ISR */
  TST_IRQHandler = Irq_osMessageQueueNew_1;
  MessageQueueId = (osMessageQueueId_t)(-1);
  SetPendingIRQ(IRQ_A);
  ASSERT_TRUE (MessageQueueId == NULL);
#endif
}

/*-----------------------------------------------------------------------------
 * TC_osMessageQueueNew_1: ISR handler
 *----------------------------------------------------------------------------*/
#if (TC_OSMESSAGEQUEUENEW_1_EN)
void Irq_osMessageQueueNew_1 (void) {
  MessageQueueId = osMessageQueueNew (1U, 4U, NULL);
}
#endif

/*=======0=========1=========2=========3=========4=========5=========6=========7=========8=========9=========0=========1====*/
/**
\brief Test case: TC_osMessageQueueNew_2
\details
  - Call osMessageQueueNew to create message queue object and assign a name to it
*/
void TC_osMessageQueueNew_2 (void) {
#if (TC_OSMESSAGEQUEUENEW_2_EN)
  osMessageQueueAttr_t attr = {NULL, 0U, NULL, 0U, NULL, 0U};
  osMessageQueueId_t id;

  /* Call osMessageQueueNew to create message queue object and assign a name to it */
  attr.name = "MessageQueue";

  id = osMessageQueueNew (1U, 4U, &attr);
  ASSERT_TRUE (id != NULL);

  /* Delete created message queue */
  ASSERT_TRUE (osMessageQueueDelete(id) == osOK);
#endif
}

/*=======0=========1=========2=========3=========4=========5=========6=========7=========8=========9=========0=========1====*/
/**
\brief Test case: TC_osMessageQueueNew_3
\details
  - Call osMessageQueueNew to create message queue object by specifying memory for control block and data in attributes
*/
void TC_osMessageQueueNew_3 (void) {
#if (TC_OSMESSAGEQUEUENEW_3_EN)
  osMessageQueueAttr_t attr = {NULL, 0U, NULL, 0U, NULL, 0U};
  osMessageQueueId_t id;

  /* Call osMessageQueueNew to create message queue object by specifying memory for control block and data in attributes */
  attr.cb_mem  = &MessageQueue_CbMem;
  attr.cb_size = sizeof(MessageQueue_CbMem);
  attr.mq_mem  = &MessageQueue_DataMem;
  attr.mq_size = sizeof(MessageQueue_DataMem);

  id = osMessageQueueNew (1U, 4U, &attr);
  ASSERT_TRUE (id != NULL);

  /* Delete created message queue */
  ASSERT_TRUE (osMessageQueueDelete(id) == osOK);
#endif
}

/*=======0=========1=========2=========3=========4=========5=========6=========7=========8=========9=========0=========1====*/
/**
\brief Test case: TC_osMessageQueueGetName_1
\details
  - Call osMessageQueueGetName to retrieve a name of an unnamed message queue
  - Call osMessageQueueGetName to retrieve a name of a message queue with assigned name
  - Call osMessageQueueGetName from ISR
  - Call osMessageQueueGetName with null object
*/
void TC_osMessageQueueGetName_1 (void) {
#if (TC_OSMESSAGEQUEUEGETNAME_1_EN)
  osMessageQueueAttr_t attr = {NULL, 0U, NULL, 0U, NULL, 0U};
  osMessageQueueId_t id;
  char const *name = "MessageQueue";

  /* Create message queue object without assigned name */
  attr.name = NULL;
  id = osMessageQueueNew (1U, 4U, &attr);
  ASSERT_TRUE (id != NULL);

  /* Call osMessageQueueGetName to retrieve a name of an unnamed message queue */
  ASSERT_TRUE(osMessageQueueGetName (id) == NULL);

  /* Delete message queue object */
  osMessageQueueDelete (id);


  /* Create message queue object with name assigned via attributes */
  attr.name = name;
  id = osMessageQueueNew (1U, 4U, &attr);
  ASSERT_TRUE (id != NULL);

  /* Call osMessageQueueGetName to retrieve a name of a message queue with assigned name */
  ASSERT_TRUE (strcmp(osMessageQueueGetName(id), name) == 0U);

  /* Call osMessageQueueGetName from ISR */
  TST_IRQHandler = Irq_osMessageQueueGetName_1;
  MessageQueueId   = id;
  MessageQueueName = name;
  SetPendingIRQ(IRQ_A);
  ASSERT_TRUE (strcmp(MessageQueueName, name) == 0U);

  /* Delete message queue object */
  osMessageQueueDelete (id);

  /* Call osMessageQueueGetName with null object */
  ASSERT_TRUE (osMessageQueueGetName (NULL) == NULL);
#endif
}

/*-----------------------------------------------------------------------------
 * TC_osMessageQueueGetName_1: ISR handler
 *----------------------------------------------------------------------------*/
#if (TC_OSMESSAGEQUEUEGETNAME_1_EN)
void Irq_osMessageQueueGetName_1 (void) {
  MessageQueueName = osMessageQueueGetName (MessageQueueId);
}
#endif

/*=======0=========1=========2=========3=========4=========5=========6=========7=========8=========9=========0=========1====*/
/**
\brief Test case: TC_osMessageQueuePut_1
\details
  - Call osMessageQueuePut to put message into the queue
  - Call osMessageQueuePut from ISR with timeout == 0
  - Call osMessageQueuePut from ISR with timeout != 0
  - Call osMessageQueuePut with null object
  - Call osMessageQueuePut from ISR with null object
*/
void TC_osMessageQueuePut_1 (void) {
#if (TC_OSMESSAGEQUEUEPUT_1_EN)
  osMessageQueueId_t id;
  uint32_t msg = 2U;

  /* Create a message queue */
  id = osMessageQueueNew (MSGQ_CNT, MSGQ_SZ, NULL);
  ASSERT_TRUE (id != NULL);

  /* Call osMessageQueuePut to put message into the queue */
  ASSERT_TRUE (osMessageQueuePut (id, &msg, 0U, 0U) == osOK);

  /* Delete Message Queue */
  ASSERT_TRUE (osMessageQueueDelete (id) == osOK);


  /* Create a message queue */
  id = osMessageQueueNew (MSGQ_CNT, MSGQ_SZ, NULL);
  ASSERT_TRUE (id != NULL);

  /* Call osMessageQueuePut from ISR */
  TST_IRQHandler = Irq_osMessageQueuePut_1;
  MessageQueueId = id;

  /* Call osMessageQueuePut from ISR with timeout == 0 */
  Isr_u32 = 0U;
  Isr_osStatus = osErrorISR;
  SetPendingIRQ(IRQ_A);
  ASSERT_TRUE (Isr_osStatus == osOK);

  /* Call osMessageQueuePut from ISR with timeout != 0 */
  Isr_u32 = 1U;
  Isr_osStatus = osOK;
  SetPendingIRQ(IRQ_A);
  ASSERT_TRUE (Isr_osStatus == osErrorParameter);

  /* Delete Message Queue */
  ASSERT_TRUE (osMessageQueueDelete (id) == osOK);

  /* Call osMessageQueuePut with null object */
  ASSERT_TRUE (osMessageQueuePut (NULL, &msg, 0U, osWaitForever) == osErrorParameter);

  /* Call osMessageQueuePut from ISR with null object */
  Isr_u32 = 2U;
  Isr_osStatus = osOK;
  SetPendingIRQ(IRQ_A);
  ASSERT_TRUE (Isr_osStatus == osErrorParameter);
#endif
}

/*-----------------------------------------------------------------------------
 * TC_osMessageQueuePut_1: ISR handler
 *----------------------------------------------------------------------------*/
#if (TC_OSMESSAGEQUEUEPUT_1_EN)
void Irq_osMessageQueuePut_1 (void) {
  uint32_t msg = 3U;

  switch (Isr_u32) {
    case 0:
      /* Call osMessageQueuePut from ISR with timeout == 0 */
      Isr_osStatus = osMessageQueuePut (MessageQueueId, &msg, 0U, 0U);
      break;

    case 1:
      /* Call osMessageQueuePut from ISR with timeout != 0 */
      Isr_osStatus = osMessageQueuePut (MessageQueueId, &msg, 0U, osWaitForever);
      break;

    case 2:
      /* Call osMessageQueuePut from ISR with null object */
      Isr_osStatus = osMessageQueuePut (NULL, &msg, 0U, 0U);
      break;
  }
}
#endif

/*=======0=========1=========2=========3=========4=========5=========6=========7=========8=========9=========0=========1====*/
/**
\brief Test case: TC_osMessageQueuePut_2
\details
  - Call osMessageQueuePut from ISR to put all available messages into the message queue
*/
void TC_osMessageQueuePut_2 (void) {
#if (TC_OSMESSAGEQUEUEPUT_2_EN)
  osMessageQueueId_t id;
  uint32_t cnt;
  uint32_t msg;
  uint32_t msg_out;

  /* Create a message queue */
  id = osMessageQueueNew (MSGQ_CNT, MSGQ_SZ, NULL);
  ASSERT_TRUE (id != NULL);

  /* Call osMessageQueuePut from ISR to put all available messages into the message queue */
  TST_IRQHandler = Irq_osMessageQueuePut_2;
  MessageQueueId = id;
  SetPendingIRQ(IRQ_A);

  /* Retrieve all queued messages */
  msg = 1U;
  cnt = MSGQ_CNT;

  while (cnt--) {
    ASSERT_TRUE (osMessageQueueGet (id, &msg_out, NULL, 0U) == osOK);
    ASSERT_TRUE (msg == msg_out);
    msg++;
  }
  /* Check that the message queue is empty */
  ASSERT_TRUE (osMessageQueueGetSpace (id) == MSGQ_CNT);

  /* Call osMessageQueueGet when the message queue is empty */
  ASSERT_TRUE (osMessageQueueGet (id, &msg_out, NULL, 0U) == osErrorResource);

  /* Delete Message Queue */
  ASSERT_TRUE (osMessageQueueDelete (id) == osOK);

#endif
}

/*-----------------------------------------------------------------------------
 * TC_osMessageQueuePut_2: ISR handler
 *----------------------------------------------------------------------------*/
#if (TC_OSMESSAGEQUEUEPUT_2_EN)
void Irq_osMessageQueuePut_2 (void) {
  uint32_t cnt;
  uint32_t msg;

  /* Check that the number of available message slots is correct */
  ASSERT_TRUE (osMessageQueueGetSpace (MessageQueueId) == MSGQ_CNT);

  /* Fill the message queue with messages */
  msg = 1U;
  cnt = MSGQ_CNT;

  while (cnt--) {
    ASSERT_TRUE (osMessageQueuePut (MessageQueueId, &msg, 0U, 0U) == osOK);
    msg++;
  }

  /* Call osMessageQueuePut when the message queue is full */
  ASSERT_TRUE (osMessageQueuePut (MessageQueueId, &msg, 0U, 0U) == osErrorResource);
}
#endif

/*=======0=========1=========2=========3=========4=========5=========6=========7=========8=========9=========0=========1====*/
/**
\brief Test case: TC_osMessageQueueGet_1
\details
  - Call osMessageQueueGet to get message from the queue
  - Call osMessageQueueGet from ISR with timeout == 0
  - Call osMessageQueueGet from ISR with timeout != 0
  - Call osMessageQueueGet with null object
  - Call osMessageQueueGet from ISR with null object
*/
void TC_osMessageQueueGet_1 (void) {
#if (TC_OSMESSAGEQUEUEGET_1_EN)
  osMessageQueueId_t id;
  uint32_t msg_in;
  uint32_t msg;

  /* Create a message queue */
  id = osMessageQueueNew (MSGQ_CNT, MSGQ_SZ, NULL);
  ASSERT_TRUE (id != NULL);

  /* Put message into the queue */
  msg_in = 2U;
  ASSERT_TRUE (osMessageQueuePut (id, &msg_in, 0U, 0U) == osOK);

  /* Call osMessageQueueGet to get message from the queue */
  ASSERT_TRUE (osMessageQueueGet (id, &msg, 0U, 0U) == osOK);

  /* Check that correct message was retrieved */
  ASSERT_TRUE (msg == msg_in);

  /* Delete Message Queue */
  ASSERT_TRUE (osMessageQueueDelete (id) == osOK);


  /* Create a message queue */
  id = osMessageQueueNew (MSGQ_CNT, MSGQ_SZ, NULL);
  ASSERT_TRUE (id != NULL);

  /* Put message into the queue */
  msg_in = 2U;
  ASSERT_TRUE (osMessageQueuePut (id, &msg_in, 0U, 0U) == osOK);

  /* Call osMessageQueueGet from ISR */
  TST_IRQHandler = Irq_osMessageQueueGet_1;
  MessageQueueId = id;

  /* Call osMessageQueueGet from ISR with timeout == 0 */
  Isr_s32 = 0;
  Isr_osStatus = osErrorISR;
  SetPendingIRQ(IRQ_A);
  ASSERT_TRUE (Isr_osStatus == osOK);
  ASSERT_TRUE (Isr_u32 = msg_in);

  /* Call osMessageQueueGet from ISR with timeout != 0 */
  Isr_s32 = 1;
  Isr_osStatus = osOK;
  SetPendingIRQ(IRQ_A);
  ASSERT_TRUE (Isr_osStatus == osErrorParameter);

  /* Delete Message Queue */
  ASSERT_TRUE (osMessageQueueDelete (id) == osOK);

  /* Call osMessageQueueGet with null object */
  ASSERT_TRUE (osMessageQueueGet (NULL, &msg, 0U, osWaitForever) == osErrorParameter);

  /* Call osMessageQueueGet from ISR with null object */
  Isr_s32 = 2;
  Isr_osStatus = osOK;
  SetPendingIRQ(IRQ_A);
  ASSERT_TRUE (Isr_osStatus == osErrorParameter);
#endif
}

/*-----------------------------------------------------------------------------
 * TC_osMessageQueueGet_1: ISR handler
 *----------------------------------------------------------------------------*/
#if (TC_OSMESSAGEQUEUEGET_1_EN)
void Irq_osMessageQueueGet_1 (void) {
  uint32_t msg = 0U;

  switch (Isr_s32) {
    case 0:
      /* Call osMessageQueueGet from ISR with timeout == 0 */
      Isr_osStatus = osMessageQueueGet (MessageQueueId, &msg, 0U, 0U);
      break;

    case 1:
      /* Call osMessageQueueGet from ISR with timeout != 0 */
      Isr_osStatus = osMessageQueueGet (MessageQueueId, &msg, 0U, osWaitForever);
      break;

    case 2:
      /* Call osMessageQueueGet from ISR with null object */
      Isr_osStatus = osMessageQueueGet (NULL, &msg, 0U, 0U);
      break;
  }

  Isr_u32 = msg;
}
#endif

/*=======0=========1=========2=========3=========4=========5=========6=========7=========8=========9=========0=========1====*/
/**
\brief Test case: TC_osMessageQueueGet_2
\details
  - Call osMessageQueueGet from ISR to retrieve all available messages
*/
void TC_osMessageQueueGet_2 (void) {
#if (TC_OSMESSAGEQUEUEGET_2_EN)
  osMessageQueueId_t id;
  uint32_t cnt;
  uint32_t msg;

  /* Create a message queue */
  id = osMessageQueueNew (MSGQ_CNT, MSGQ_SZ, NULL);
  ASSERT_TRUE (id != NULL);

  /* Fill the message queue with messages */
  msg = 1U;
  cnt = MSGQ_CNT;

  while (cnt--) {
    ASSERT_TRUE (osMessageQueuePut (id, &msg, 0U, 0U) == osOK);
    msg++;
  }
  /* Check that the message queue is full */
  ASSERT_TRUE (osMessageQueueGetSpace (id) == 0U);

  /* Call osMessageQueuePut when the message queue is full */
  ASSERT_TRUE (osMessageQueuePut (id, &msg, 0U, 0U) == osErrorResource);

  /* Call osMessageQueueGet from ISR to retrieve all queued messages */
  TST_IRQHandler = Irq_osMessageQueueGet_2;
  MessageQueueId = id;
  SetPendingIRQ(IRQ_A);

  /* Delete Message Queue */
  ASSERT_TRUE (osMessageQueueDelete (id) == osOK);
#endif
}

/*-----------------------------------------------------------------------------
 * TC_osMessageQueueGet_2: ISR handler
 *----------------------------------------------------------------------------*/
#if (TC_OSMESSAGEQUEUEGET_2_EN)
void Irq_osMessageQueueGet_2 (void) {
  uint32_t cnt;
  uint32_t msg;
  uint32_t msg_out;

  /* Check that the number of enqueued messages is correct */
  ASSERT_TRUE (osMessageQueueGetCount(MessageQueueId) == MSGQ_CNT);

  msg = 1U;
  cnt = MSGQ_CNT;

  while (cnt--) {
    ASSERT_TRUE (osMessageQueueGet (MessageQueueId, &msg_out, NULL, 0U) == osOK);
    ASSERT_TRUE (msg == msg_out);
    msg++;
  }

  /* Call osMessageQueueGet when the message queue is empty */
  ASSERT_TRUE (osMessageQueueGet (MessageQueueId, &msg_out, NULL, 0U) == osErrorResource);
}
#endif

/*=======0=========1=========2=========3=========4=========5=========6=========7=========8=========9=========0=========1====*/
/**
\brief Test case: TC_osMessageQueueGetCapacity_1
\details
  - Call osMessageQueueGetCapacity to retrieve the maximum number of messages in the message queue
  - Call osMessageQueueGetCapacity from ISR
  - Call osMessageQueueGetCapacity from ISR with null object
  - Call osMessageQueueGetCapacity with null object
*/
void TC_osMessageQueueGetCapacity_1 (void) {
#if (TC_OSMESSAGEQUEUEGETCAPACITY_1_EN)
  osMessageQueueId_t id;

  /* Create a message queue */
  id = osMessageQueueNew (MSGQ_CNT, MSGQ_SZ, NULL);
  ASSERT_TRUE (id != NULL);

  /* Call osMessageQueueGetCapacity to retrieve the maximum number of messages in the message queue */
  ASSERT_TRUE (osMessageQueueGetCapacity (id) == MSGQ_CNT);

  /* Call osMessageQueueGetCapacity from ISR */
  TST_IRQHandler = Irq_osMessageQueueGetCapacity_1;
  MessageQueueId = id;
  Isr_s32 = 0;
  Isr_u32 = 0U;
  SetPendingIRQ(IRQ_A);
  ASSERT_TRUE (Isr_u32 == MSGQ_CNT);

  /* Call osMessageQueueGetCapacity from ISR with null object */
  Isr_s32 = 1;
  Isr_u32 = MSGQ_CNT;
  SetPendingIRQ(IRQ_A);
  ASSERT_TRUE (Isr_u32 == 0U);

  /* Delete Message Queue */
  ASSERT_TRUE (osMessageQueueDelete (id) == osOK);

  /* Call osMessageQueueGetCapacity with null object */
  ASSERT_TRUE (osMessageQueueGetCapacity (NULL) == 0U);
#endif
}
/*-----------------------------------------------------------------------------
 * TC_osMessageQueueGetCapacity_1: ISR handler
 *----------------------------------------------------------------------------*/
#if (TC_OSMESSAGEQUEUEGETCAPACITY_1_EN)
void Irq_osMessageQueueGetCapacity_1 (void) {

  switch (Isr_s32) {
    case 0:
      /* Call osMessageQueueGetCapacity from ISR */
      Isr_u32 = osMessageQueueGetCapacity (MessageQueueId);
      break;

    case 1:
      /* Call osMessageQueueGetCapacity from ISR with null object */
      Isr_u32 = osMessageQueueGetCapacity (NULL);
      break;
  }
}
#endif

/*=======0=========1=========2=========3=========4=========5=========6=========7=========8=========9=========0=========1====*/
/**
\brief Test case: TC_osMessageQueueGetMsgSize_1
\details
  - Call osMessageQueueGetMsgSize to retrieve the maximum message size
  - Call osMessageQueueGetMsgSize from ISR
  - Call osMessageQueueGetMsgSize from ISR with null object
  - Call osMessageQueueGetMsgSize with null object
*/
void TC_osMessageQueueGetMsgSize_1 (void) {
#if (TC_OSMESSAGEQUEUEGETMSGSIZE_1_EN)
  osMessageQueueId_t id;

  /* Create a message queue */
  id = osMessageQueueNew (MSGQ_CNT, MSGQ_SZ, NULL);
  ASSERT_TRUE (id != NULL);

  /* Call osMessageQueueGetMsgSize to retrieve the maximum message size */
  ASSERT_TRUE (osMessageQueueGetMsgSize (id) == MSGQ_SZ);

  /* Call osMessageQueueGetMsgSize from ISR */
  TST_IRQHandler = Irq_osMessageQueueGetMsgSize_1;
  MessageQueueId = id;
  Isr_s32 = 0;
  Isr_u32 = 0U;
  SetPendingIRQ(IRQ_A);
  ASSERT_TRUE (Isr_u32 == MSGQ_SZ);

  /* Call osMessageQueueGetMsgSize from ISR with null object */
  Isr_s32 = 1;
  Isr_u32 = MSGQ_SZ;
  SetPendingIRQ(IRQ_A);
  ASSERT_TRUE (Isr_u32 == 0U);

  /* Delete Message Queue */
  ASSERT_TRUE (osMessageQueueDelete (id) == osOK);

  /* Call osMessageQueueGetMsgSize with null object */
  ASSERT_TRUE (osMessageQueueGetMsgSize (NULL) == 0U);
#endif
}
/*-----------------------------------------------------------------------------
 * TC_osMessageQueueGetMsgSize_1: ISR handler
 *----------------------------------------------------------------------------*/
#if (TC_OSMESSAGEQUEUEGETMSGSIZE_1_EN)
void Irq_osMessageQueueGetMsgSize_1 (void) {

  switch (Isr_s32) {
    case 0:
      /* Call osMessageQueueGetMsgSize from ISR */
      Isr_u32 = osMessageQueueGetMsgSize (MessageQueueId);
      break;

    case 1:
      /* Call osMessageQueueGetMsgSize from ISR with null object */
      Isr_u32 = osMessageQueueGetMsgSize (NULL);
      break;
  }
}
#endif

/*=======0=========1=========2=========3=========4=========5=========6=========7=========8=========9=========0=========1====*/
/**
\brief Test case: TC_osMessageQueueGetCount_1
\details
  - Call osMessageQueueGetCount to retrieve the number of queued messages
  - Call osMessageQueueGetCount from ISR
  - Call osMessageQueueGetCount from ISR with null object
  - Call osMessageQueueGetCount with null object
*/
void TC_osMessageQueueGetCount_1 (void) {
#if (TC_OSMESSAGEQUEUEGETCOUNT_1_EN)
  osMessageQueueId_t id;
  uint32_t msg;

  /* Create a message queue */
  id = osMessageQueueNew (MSGQ_CNT, MSGQ_SZ, NULL);
  ASSERT_TRUE (id != NULL);

  /* Put message into the queue */
  msg = 2U;
  ASSERT_TRUE (osMessageQueuePut (id, &msg, 0U, 0U) == osOK);

  /* Call osMessageQueueGetCount to retrieve the number of queued messages */
  ASSERT_TRUE (osMessageQueueGetCount (id) == 1U);

  /* Call osMessageQueueGetCount from ISR */
  TST_IRQHandler = Irq_osMessageQueueGetCount_1;
  MessageQueueId = id;
  Isr_s32 = 0;
  Isr_u32 = 0U;
  SetPendingIRQ(IRQ_A);
  ASSERT_TRUE (Isr_u32 == 1U);

  /* Call osMessageQueueGetCount from ISR with null object */
  Isr_s32 = 1;
  Isr_u32 = MSGQ_CNT;
  SetPendingIRQ(IRQ_A);
  ASSERT_TRUE (Isr_u32 == 0U);

  /* Delete Message Queue */
  ASSERT_TRUE (osMessageQueueDelete (id) == osOK);

  /* Call osMessageQueueGetCount with null object */
  ASSERT_TRUE (osMessageQueueGetCount (NULL) == 0U);
#endif
}
/*-----------------------------------------------------------------------------
 * TC_osMessageQueueGetCount_1: ISR handler
 *----------------------------------------------------------------------------*/
#if (TC_OSMESSAGEQUEUEGETCOUNT_1_EN)
void Irq_osMessageQueueGetCount_1 (void) {

  switch (Isr_s32) {
    case 0:
      /* Call osMessageQueueGetCount from ISR */
      Isr_u32 = osMessageQueueGetCount (MessageQueueId);
      break;

    case 1:
      /* Call osMessageQueueGetCount from ISR with null object */
      Isr_u32 = osMessageQueueGetCount (NULL);
      break;
  }
}
#endif

/*=======0=========1=========2=========3=========4=========5=========6=========7=========8=========9=========0=========1====*/
/**
\brief Test case: TC_osMessageQueueGetSpace_1
\details
  - Call osMessageQueueGetSpace to retrieve the number of available message slots
  - Call osMessageQueueGetSpace from ISR
  - Call osMessageQueueGetSpace from ISR with null object
  - Call osMessageQueueGetSpace with null object
*/
void TC_osMessageQueueGetSpace_1 (void) {
#if (TC_OSMESSAGEQUEUEGETSPACE_1_EN)
  osMessageQueueId_t id;
  uint32_t msg;

  /* Create a message queue */
  id = osMessageQueueNew (MSGQ_CNT, MSGQ_SZ, NULL);
  ASSERT_TRUE (id != NULL);

  /* Put message into the queue */
  msg = 2U;
  ASSERT_TRUE (osMessageQueuePut (id, &msg, 0U, 0U) == osOK);

  /* Call osMessageQueueGetSpace to retrieve the number of available message slots */
  ASSERT_TRUE (osMessageQueueGetSpace (id) == (MSGQ_CNT-1U));

  /* Call osMessageQueueGetSpace from ISR */
  TST_IRQHandler = Irq_osMessageQueueGetSpace_1;
  MessageQueueId = id;
  Isr_s32 = 0;
  Isr_u32 = 0U;
  SetPendingIRQ(IRQ_A);
  ASSERT_TRUE (Isr_u32 == (MSGQ_CNT-1U));

  /* Call osMessageQueueGetSpace from ISR with null object */
  Isr_s32 = 1;
  Isr_u32 = MSGQ_CNT;
  SetPendingIRQ(IRQ_A);
  ASSERT_TRUE (Isr_u32 == 0U);

  /* Delete Message Queue */
  ASSERT_TRUE (osMessageQueueDelete (id) == osOK);

  /* Call osMessageQueueGetSpace with null object */
  ASSERT_TRUE (osMessageQueueGetSpace (NULL) == 0U);
#endif
}

/*-----------------------------------------------------------------------------
 * TC_osMessageQueueGetSpace_1: ISR handler
 *----------------------------------------------------------------------------*/
#if (TC_OSMESSAGEQUEUEGETSPACE_1_EN)
void Irq_osMessageQueueGetSpace_1 (void) {

  switch (Isr_s32) {
    case 0:
      /* Call osMessageQueueGetSpace from ISR */
      Isr_u32 = osMessageQueueGetSpace (MessageQueueId);
      break;

    case 1:
      /* Call osMessageQueueGetSpace from ISR with null object */
      Isr_u32 = osMessageQueueGetSpace (NULL);
      break;
  }
}
#endif

/*=======0=========1=========2=========3=========4=========5=========6=========7=========8=========9=========0=========1====*/
/**
\brief Test case: TC_osMessageQueueReset_1
\details
  - Call osMessageQueueReset from ISR
  - Call osMessageQueueReset with null object id
*/
void TC_osMessageQueueReset_1 (void) {
#if (TC_OSMESSAGEQUEUERESET_1_EN)
  osMessageQueueId_t id;
  uint32_t msg;

  /* Create a message queue */
  id = osMessageQueueNew (MSGQ_CNT, MSGQ_SZ, NULL);
  ASSERT_TRUE (id != NULL);

  /* Put message into the queue */
  msg = 2U;
  ASSERT_TRUE (osMessageQueuePut (id, &msg, 0U, 0U) == osOK);

  /* Call osMessageQueueReset to reset the message queue */
  ASSERT_TRUE (osMessageQueueReset (id) == osOK);

  /* Check that the message queue was reset */
  ASSERT_TRUE (osMessageQueueGetSpace (id) == MSGQ_CNT);

  /* Call osMessageQueueReset from ISR */
  TST_IRQHandler = Irq_osMessageQueueReset_1;
  MessageQueueId = id;
  Isr_osStatus = osOK;
  SetPendingIRQ(IRQ_A);
  ASSERT_TRUE (Isr_osStatus == osErrorISR);

  /* Delete message queue */
  ASSERT_TRUE (osMessageQueueDelete (id) == osOK);

  /* Call osMessageQueueReset with null object id */
  ASSERT_TRUE (osMessageQueueReset (NULL) == osErrorParameter);
#endif
}

/*-----------------------------------------------------------------------------
 * TC_osMessageQueueReset_1: ISR handler
 *----------------------------------------------------------------------------*/
#if (TC_OSMESSAGEQUEUERESET_1_EN)
void Irq_osMessageQueueReset_1 (void) {
  Isr_osStatus = osMessageQueueReset (MessageQueueId);
}
#endif

/*=======0=========1=========2=========3=========4=========5=========6=========7=========8=========9=========0=========1====*/
/**
\brief Test case: TC_osMessageQueueDelete_1
\details
  - Call osMessageQueueDelete to delete empty message queue
  - Call osMessageQueueDelete to delete non-empty message queue
  - Call osMessageQueueDelete from ISR
  - Call osMessageQueueDelete with null object
*/
void TC_osMessageQueueDelete_1 (void) {
#if (TC_OSMESSAGEQUEUEDELETE_1_EN)
  osMessageQueueId_t id;
  uint32_t msg;

  /* Create a message queue */
  id = osMessageQueueNew (MSGQ_CNT, MSGQ_SZ, NULL);
  ASSERT_TRUE (id != NULL);

  /* Call osMessageQueueDelete to delete empty message queue */
  ASSERT_TRUE (osMessageQueueDelete (id) == osOK);

  /* Create a message queue */
  id = osMessageQueueNew (MSGQ_CNT, MSGQ_SZ, NULL);
  ASSERT_TRUE (id != NULL);

  /* Put message into the queue */
  msg = 2U;
  ASSERT_TRUE (osMessageQueuePut (id, &msg, 0U, 0U) == osOK);

  /* Call osMessageQueueDelete to delete non-empty message queue */
  ASSERT_TRUE (osMessageQueueDelete (id) == osOK);

  /* Create a message queue */
  id = osMessageQueueNew (MSGQ_CNT, MSGQ_SZ, NULL);
  ASSERT_TRUE (id != NULL);

  /* Call osMessageQueueDelete from ISR */
  TST_IRQHandler = Irq_osMessageQueueDelete_1;
  Isr_osStatus = osOK;
  MessageQueueId = id;
  SetPendingIRQ(IRQ_A);
  ASSERT_TRUE (Isr_osStatus == osErrorISR);

  /* Delete the message queue */
  ASSERT_TRUE (osMessageQueueDelete (id) == osOK);

  /* Call osMessageQueueDelete with null object */
  ASSERT_TRUE (osMessageQueueDelete (NULL) == osErrorParameter);
#endif
}

/*-----------------------------------------------------------------------------
 * TC_osMessageQueueDelete_1: ISR handler
 *----------------------------------------------------------------------------*/
#if (TC_OSMESSAGEQUEUEDELETE_1_EN)
void Irq_osMessageQueueDelete_1 (void) {
  Isr_osStatus = osMessageQueueDelete (MessageQueueId);
}
#endif

/*=======0=========1=========2=========3=========4=========5=========6=========7=========8=========9=========0=========1====*/
/**
\brief Test case: TC_MsgQBasic
\details
- Fill message queue with messages
- Get all messages from queue
- Check if messages are correct
*/
void TC_MsgQBasic (void) {
#if (TC_MSGQBASIC_EN)
  osStatus_t stat;
  uint32_t i, txi, rxi;

  /* Create a message queue */
  MessageQueueId = osMessageQueueNew (MSGQ_CNT, MSGQ_SZ, NULL);
  ASSERT_TRUE (MessageQueueId != NULL);

  if (MessageQueueId != NULL) {

    ASSERT_TRUE (osMessageQueueGetCapacity (MessageQueueId) == MSGQ_CNT);
    ASSERT_TRUE (osMessageQueueGetMsgSize  (MessageQueueId) == MSGQ_SZ);

    /* - Fill message queue with messages */
    for (txi = 0, i = 0; i < MSGQ_CNT; i++, txi++) {
      ASSERT_TRUE (osMessageQueuePut (MessageQueueId, &txi, 0, 0) == osOK);
      ASSERT_TRUE (osMessageQueueGetCount (MessageQueueId) == i+1);
      ASSERT_TRUE (osMessageQueueGetSpace (MessageQueueId) == MSGQ_CNT-i-1);
    }
    /* Message queue full, check resource error */
    ASSERT_TRUE (osMessageQueuePut (MessageQueueId, &txi, 0, 0) == osErrorResource);
    /* Message queue full, check timeout error */
    ASSERT_TRUE (osMessageQueuePut (MessageQueueId, &txi, 0, 10) == osErrorTimeout);

    /* - Get all messages from queue */
    for (txi = 0, i = 0; i < MSGQ_CNT; i++, txi++) {
      stat = osMessageQueueGet (MessageQueueId, &rxi, NULL, 0);
      ASSERT_TRUE (stat == osOK);
      /* - Check if messages are correct */
      if (stat == osOK) {
        ASSERT_TRUE (rxi == txi);
      }
      ASSERT_TRUE (osMessageQueueGetCount (MessageQueueId) == MSGQ_CNT-i-1);
      ASSERT_TRUE (osMessageQueueGetSpace (MessageQueueId) == i+1);
    }
    /* Message queue empty, check resource error */
    ASSERT_TRUE (osMessageQueueGet (MessageQueueId, &rxi, NULL,  0) == osErrorResource);
    /* Message queue empty, check timeout error */
    ASSERT_TRUE (osMessageQueueGet (MessageQueueId, &rxi, NULL, 10) == osErrorTimeout);

    /* - Fill message queue with messages */
    for (txi = 0, i = 0; i < MSGQ_CNT; i++, txi++) {
      ASSERT_TRUE (osMessageQueuePut (MessageQueueId, &txi, 0, 0) == osOK);
    }
    ASSERT_TRUE (osMessageQueueGetCount (MessageQueueId) == MSGQ_CNT);
    ASSERT_TRUE (osMessageQueueGetSpace (MessageQueueId) == 0);
    /* - Reset message queue */
    ASSERT_TRUE (osMessageQueueReset(MessageQueueId) == osOK);
    ASSERT_TRUE (osMessageQueueGetCount (MessageQueueId) == 0);
    ASSERT_TRUE (osMessageQueueGetSpace (MessageQueueId) == MSGQ_CNT);

    /* Delete Message Queue */
    ASSERT_TRUE (osMessageQueueDelete (MessageQueueId) == osOK);
  }
#endif
}

/*=======0=========1=========2=========3=========4=========5=========6=========7=========8=========9=========0=========1====*/
/**
\brief Test case: TC_MsgQWait
\details
- Reset global counter
- Create a thread that increments a counter and waits for message
- Verify if counter incremented
- Send message to the waiting thread
- Verify if counter incremented
- Verify if message received
*/
void TC_MsgQWait (void) {
#if (TC_MSGQWAIT_EN)
  osThreadAttr_t attr = { NULL, osThreadDetached, NULL, 0U, NULL, 0U, osPriorityAboveNormal, 0U, 0U};
  uint32_t cnt = 0;
  uint32_t msg = 2;

  /* Create a message queue */
  MessageQueueId = osMessageQueueNew (MSGQ_CNT, MSGQ_SZ, NULL);
  ASSERT_TRUE (MessageQueueId != NULL);

  if (MessageQueueId != NULL) {
    /* - Reset global counter */
    MsgWaitCnt = 0;
    /* - Create a thread that increments a counter and waits for message */
    ASSERT_TRUE (osThreadNew (Th_MsgQWait, &cnt, &attr) != NULL);
    /* - Verify if counter incremented */
    ASSERT_TRUE (MsgWaitCnt == 1);
    /* - Send message to the waiting thread */
    ASSERT_TRUE (osMessageQueuePut (MessageQueueId, &msg, 0, osWaitForever) == osOK);
    /* - Verify if counter incremented */
    ASSERT_TRUE (MsgWaitCnt == 2);
    /* - Verify if message received */
    ASSERT_TRUE (MsgWaitCnt == cnt);

    /* Delete Message Queue */
    ASSERT_TRUE (osMessageQueueDelete (MessageQueueId) == osOK);
  }
#endif
}

/*-----------------------------------------------------------------------------
 * TC_MsgQWait: Helper thread
 *----------------------------------------------------------------------------*/
#if (TC_MSGQWAIT_EN)
void Th_MsgQWait (void *arg) {
  uint32_t *p = (uint32_t *)arg;
  osStatus_t stat;
  uint32_t msg;

  while (1) {
    /* Increment a counter */
    MsgWaitCnt++;
    /* Wait until message arrives */
    stat = osMessageQueueGet (MessageQueueId, &msg, NULL, osWaitForever);
    ASSERT_TRUE (stat == osOK);
    /* Increment a counter */
    MsgWaitCnt++;

    if (stat == osOK) {
      /* Return counter value */
      *p = msg;

      /* Explicitly terminate this thread */
      osThreadTerminate (osThreadGetId());
      return;
    }
  }
}
#endif

/*=======0=========1=========2=========3=========4=========5=========6=========7=========8=========9=========0=========1====*/
/**
\brief Test case: TC_MsgQCheckTimeout
\details
- Set time thresholds
- Create wakeup thread to put a message after 10 ticks
- Wait for a message with a defined timeout
- Check if the message is obtained between the minimum and maximum thresholds
- Wait for a message with an infinite timeout
- Check if the message is obtained between the minimum and maximum thresholds
*/
void TC_MsgQCheckTimeout (void) {
#if (TC_MSGQCHECKTIMEOUT_EN)
  osThreadAttr_t attr = { NULL, osThreadDetached, NULL, 0U, NULL, 0U, osPriorityAboveNormal, 0U, 0U};
  osThreadId_t id;
  osStatus_t stat;
  uint32_t msg = 1;
  uint32_t t_10;

  /* Create a message queue */
  MessageQueueId = osMessageQueueNew (MSGQ_CNT, MSGQ_SZ, NULL);
  ASSERT_TRUE (MessageQueueId != NULL);

  /* Get main thread ID */
  ThreadId = osThreadGetId ();
  ASSERT_TRUE (ThreadId != NULL);

  /* Synchronize tick */
  osDelay(1U);

  /* Create wakeup thread to put a message after 10 ticks */
  id = osThreadNew(Th_MsgQWakeup, NULL, &attr);

  if (id != NULL) {
    t_10 = osKernelGetTickCount();
    stat = osMessageQueueGet (MessageQueueId, &msg, NULL, 100);
    t_10 = osKernelGetTickCount() - t_10;

    ASSERT_TRUE (stat == osOK);
    ASSERT_TRUE (t_10 == 10U);
  }
  else {
    ASSERT_TRUE (id != NULL);
  }

  /* Wait until wakeup thread is terminated */
  osDelay(5U);

  /* Create wakeup thread to put a message after 10 ticks */
  id = osThreadNew(Th_MsgQWakeup, NULL, &attr);

  if (id != NULL) {
    t_10 = osKernelGetTickCount();
    stat = osMessageQueueGet (MessageQueueId, &msg, NULL, osWaitForever);
    t_10 = osKernelGetTickCount() - t_10;

    ASSERT_TRUE (stat == osOK);
    ASSERT_TRUE (t_10 == 10U);
  }
  else {
    ASSERT_TRUE (id != NULL);
  }

  /* Wait until wakeup thread is terminated */
  osDelay(5U);

  /* Delete Message Queue */
  ASSERT_TRUE (osMessageQueueDelete (MessageQueueId) == osOK);
#endif
}

/*-----------------------------------------------------------------------------
 * TC_MsgQCheckTimeout: Helper thread
 *----------------------------------------------------------------------------*/
#if (TC_MSGQCHECKTIMEOUT_EN)
void Th_MsgQWakeup (void *arg) {
  uint32_t msg;

  (void)arg;

  osDelay(10);

  /* Put message to the queue */
  ASSERT_TRUE (osMessageQueuePut (MessageQueueId, &msg, 0, 0) == osOK);

  /* Explicitly terminate this thread */
  osThreadTerminate (osThreadGetId());
}
#endif

/*=======0=========1=========2=========3=========4=========5=========6=========7=========8=========9=========0=========1====*/
/**
\brief Test case: TC_MsgQAllocation
\details
- Test message queue object allocation
*/
void TC_MsgQAllocation (void) {
#if (TC_MSGQALLOCATION_EN)
  osMessageQueueId_t id[MAX_MSGQUEUE_NUM];
  uint32_t cnt = 0U;
  uint32_t max = 0U;
  uint32_t i;

  /* Create max number of objects */
  for (i = 0U; i < MAX_MSGQUEUE_NUM; i++) {
    id[i] = osMessageQueueNew (MSGQ_CNT, MSGQ_SZ, NULL);

    if (id[i] == NULL) {
      max = i;
      break;
    }
  }
  ASSERT_TRUE (i > 0U);

  if (max > 0U) {
    /* Try to allocate extra object */
    ASSERT_TRUE(osMessageQueueNew (MSGQ_CNT, MSGQ_SZ, NULL) == NULL);
  }

  osDelay(10);

  /* Delete all */
  cnt = i;

  for (i = 0U; i < cnt; i++) {
    ASSERT_TRUE(osMessageQueueDelete(id[i]) == osOK);
  }
#endif
}

/**
@}
*/
// end of group msgqueue_funcs
