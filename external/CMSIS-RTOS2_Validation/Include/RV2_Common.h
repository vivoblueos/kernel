/*
 * Copyright (C) 2023 ARM Limited or its affiliates. All rights reserved.
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

#ifndef RV2_COMMON_H__
#define RV2_COMMON_H__

#include <stdint.h>
#include "cmsis_os2.h"

#include "RV2_Config.h"

#if defined(DEFINE_OBJECT_SIZES) && (DEFINE_OBJECT_SIZES != 0)
#define THREAD_CB_MEM_SIZE        THREAD_OBJECT_SIZE
#define TIMER_CB_MEM_SIZE         TIMER_OBJECT_SIZE
#define EVENTFLAGS_CB_MEM_SIZE    EVENT_FLAGS_OBJECT_SIZE
#define MUTEX_CB_MEM_SIZE         MUTEX_OBJECT_SIZE
#define SEMAPHORE_CB_MEM_SIZE     SEMAPHORE_OBJECT_SIZE
#define MEMORYPOOL_CB_MEM_SIZE    MEMORY_POOL_OBJECT_SIZE
#define MESSAGEQUEUE_CB_MEM_SIZE  MESSAGE_QUEUE_OBJECT_SIZE
#else
#ifndef THREAD_CB_MEM_SIZE
#define THREAD_CB_MEM_SIZE        200
#endif

#ifndef TIMER_CB_MEM_SIZE
#define TIMER_CB_MEM_SIZE         200
#endif

#ifndef EVENTFLAGS_CB_MEM_SIZE
#define EVENTFLAGS_CB_MEM_SIZE    200
#endif

#ifndef MUTEX_CB_MEM_SIZE
#define MUTEX_CB_MEM_SIZE         200
#endif

#ifndef SEMAPHORE_CB_MEM_SIZE
#define SEMAPHORE_CB_MEM_SIZE     200
#endif

#ifndef MEMORYPOOL_CB_MEM_SIZE
#define MEMORYPOOL_CB_MEM_SIZE    200
#endif

#ifndef MESSAGEQUEUE_CB_MEM_SIZE
#define MESSAGEQUEUE_CB_MEM_SIZE  200
#endif
#endif /* DEFINE_OBJECT_SIZES */

#ifndef THREAD_STACK_MEM_SIZE
#define THREAD_STACK_MEM_SIZE     200
#endif

#ifndef MEMORYPOOL_DATA_MEM_SIZE
#define MEMORYPOOL_DATA_MEM_SIZE  200
#endif

#ifndef MESSAGEQUEUE_DATA_MEM_SIZE
#define MESSAGEQUEUE_DATA_MEM_SIZE 200
#endif

/* Common variables */
extern volatile osThreadId_t       ThreadId;
extern const    char *             ThreadName;
extern          osThreadAttr_t     ThreadAttr;
extern          void *             ThreadArg;
extern          uint8_t            Thread_CbMem[THREAD_CB_MEM_SIZE];
extern          uint8_t            Thread_StackMem[THREAD_STACK_MEM_SIZE];

extern volatile osEventFlagsId_t   EventFlagsId;
extern const    char *             EventFlagsName;
extern          uint8_t            EventFlags_CbMem[EVENTFLAGS_CB_MEM_SIZE];

extern volatile osTimerId_t        TimerId;
extern const    char *             TimerName;
extern          uint8_t            Timer_CbMem[TIMER_CB_MEM_SIZE];

extern volatile osMutexId_t        MutexId;
extern const    char *             MutexName;
extern          uint8_t            Mutex_CbMem[MUTEX_CB_MEM_SIZE];

extern volatile osSemaphoreId_t    SemaphoreId;
extern const    char *             SemaphoreName;
extern          uint8_t            Semaphore_CbMem[SEMAPHORE_CB_MEM_SIZE];

extern volatile osMemoryPoolId_t   MemoryPoolId;
extern const    char *             MemoryPoolName;
extern          uint8_t            MemoryPool_CbMem[MEMORYPOOL_CB_MEM_SIZE];
extern          uint8_t            MemoryPool_DataMem[MEMORYPOOL_DATA_MEM_SIZE];

extern volatile osMessageQueueId_t MessageQueueId;
extern const    char *             MessageQueueName;
extern          uint8_t            MessageQueue_CbMem[MESSAGEQUEUE_CB_MEM_SIZE];
extern          uint8_t            MessageQueue_DataMem[MESSAGEQUEUE_DATA_MEM_SIZE];

/* Variables used in ISR */
extern volatile osKernelState_t Isr_osKernelState;
extern volatile osThreadState_t Isr_osThreadState;
extern volatile osThreadId_t    Isr_osThreadId;
extern volatile osPriority_t    Isr_osPriority;
extern volatile osStatus_t      Isr_osStatus;
extern volatile uint32_t        Isr_u32;
extern volatile int32_t         Isr_s32;
extern volatile void           *Isr_pv;


#endif /* RV2_COMMON_H__ */
