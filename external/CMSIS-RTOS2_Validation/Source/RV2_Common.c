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

#include "RV2_Common.h"
#include "cmsis_compiler.h"

/* Common variables */
volatile osThreadId_t       ThreadId;
const    char *             ThreadName;
         osThreadAttr_t     ThreadAttr;
         void *             ThreadArg;
         uint8_t            Thread_CbMem[THREAD_CB_MEM_SIZE] __ALIGNED(4);
         uint8_t            Thread_StackMem[THREAD_STACK_MEM_SIZE] __ALIGNED(8);

volatile osEventFlagsId_t   EventFlagsId;
const    char *             EventFlagsName;
         uint8_t            EventFlags_CbMem[EVENTFLAGS_CB_MEM_SIZE] __ALIGNED(4);

volatile osTimerId_t        TimerId;
const    char *             TimerName;
         uint8_t            Timer_CbMem[TIMER_CB_MEM_SIZE] __ALIGNED(4);

volatile osMutexId_t        MutexId;
const    char *             MutexName;
         uint8_t            Mutex_CbMem[MUTEX_CB_MEM_SIZE] __ALIGNED(4);

volatile osSemaphoreId_t    SemaphoreId;
const    char *             SemaphoreName;
         uint8_t            Semaphore_CbMem[SEMAPHORE_CB_MEM_SIZE] __ALIGNED(4);

volatile osMemoryPoolId_t   MemoryPoolId;
const    char *             MemoryPoolName;
         uint8_t            MemoryPool_CbMem[MEMORYPOOL_CB_MEM_SIZE] __ALIGNED(4);
         uint8_t            MemoryPool_DataMem[MEMORYPOOL_DATA_MEM_SIZE] __ALIGNED(4);

volatile osMessageQueueId_t MessageQueueId;
const    char *             MessageQueueName;
         uint8_t            MessageQueue_CbMem[MESSAGEQUEUE_CB_MEM_SIZE] __ALIGNED(4);
         uint8_t            MessageQueue_DataMem[MESSAGEQUEUE_DATA_MEM_SIZE] __ALIGNED(4);

/* Variables used in ISR */
volatile osKernelState_t Isr_osKernelState;
volatile osThreadState_t Isr_osThreadState;
volatile osThreadId_t    Isr_osThreadId;
volatile osPriority_t    Isr_osPriority;
volatile osStatus_t      Isr_osStatus;
volatile uint32_t        Isr_u32;
volatile int32_t         Isr_s32;
volatile void           *Isr_pv;
