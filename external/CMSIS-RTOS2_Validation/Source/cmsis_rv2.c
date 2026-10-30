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

#include "cmsis_rv2.h"

static const osThreadAttr_t tf_main_attr = {
  .name          = "TestRunner",
  .attr_bits     = osThreadJoinable,
  .cb_mem        = NULL,
  .cb_size       = 0U,
  .stack_mem     = NULL,
  .stack_size    = MAIN_THREAD_STACK,
  .priority      = osPriorityNormal,
  .tz_module     = 0,
  // .affinity_mask = 0
};

/*-----------------------------------------------------------------------------
 *      Init test suite
 *----------------------------------------------------------------------------*/
__WEAK void TS_Init (void) {
}

/*-----------------------------------------------------------------------------
 *      Uninit test suite
 *----------------------------------------------------------------------------*/
__WEAK void TS_Uninit (void) {
}

/*-----------------------------------------------------------------------------
 *      Enable IRQ
 *----------------------------------------------------------------------------*/
__WEAK void EnableIRQ (int32_t irq_num) {
  (void)irq_num;
}

/*-----------------------------------------------------------------------------
 *      Disable IRQ
 *----------------------------------------------------------------------------*/
__WEAK void DisableIRQ (int32_t irq_num) {
  (void)irq_num;
}

/*-----------------------------------------------------------------------------
 *      Set Pending IRQ
 *----------------------------------------------------------------------------*/
__WEAK void SetPendingIRQ (int32_t irq_num) {
  (void)irq_num;
}

/*-----------------------------------------------------------------------------
 *      Test cases list
 *----------------------------------------------------------------------------*/
static const TEST_CASE TC_List[] = {
#if (TC_OSKERNEL_EN)
  TCD ( TC_osKernelInitialize_1,          TC_OSKERNELINITIALIZE_1_EN          ),
  TCD ( TC_osKernelGetInfo_1,             TC_OSKERNELGETINFO_1_EN             ),
  TCD ( TC_osKernelGetState_1,            TC_OSKERNELGETSTATE_1_EN            ),
  TCD ( TC_osKernelGetState_2,            TC_OSKERNELGETSTATE_2_EN            ),
  TCD ( TC_osKernelStart_1,               TC_OSKERNELSTART_1_EN               ),
  TCD ( TC_osKernelLock_1,                TC_OSKERNELLOCK_1_EN                ),
  TCD ( TC_osKernelLock_2,                TC_OSKERNELLOCK_2_EN                ),
  TCD ( TC_osKernelUnlock_1,              TC_OSKERNELUNLOCK_1_EN              ),
  TCD ( TC_osKernelUnlock_2,              TC_OSKERNELUNLOCK_2_EN              ),
  TCD ( TC_osKernelRestoreLock_1,         TC_OSKERNELRESTORELOCK_1_EN         ),
  TCD ( TC_osKernelSuspend_1,             TC_OSKERNELSUSPEND_1_EN             ),
  TCD ( TC_osKernelResume_1,              TC_OSKERNELRESUME_1_EN              ),
  TCD ( TC_osKernelGetTickCount_1,        TC_OSKERNELGETTICKCOUNT_EN          ),
  TCD ( TC_osKernelGetTickFreq_1,         TC_OSKERNELGETTICKFREQ_EN           ),
  TCD ( TC_osKernelGetSysTimerCount_1,    TC_OSKERNELGETSYSTIMERCOUNT_EN      ),
  TCD ( TC_osKernelGetSysTimerFreq_1,     TC_OSKERNELGETSYSTIMERFREQ_EN       ),
#endif
#if (TC_OSTHREAD_EN)
  TCD ( TC_osThreadNew_1,                 TC_OSTHREADNEW_1_EN                 ),
  TCD ( TC_osThreadNew_2,                 TC_OSTHREADNEW_2_EN                 ),
  TCD ( TC_osThreadNew_3,                 TC_OSTHREADNEW_3_EN                 ),
  TCD ( TC_osThreadNew_4,                 TC_OSTHREADNEW_4_EN                 ),
  TCD ( TC_osThreadNew_5,                 TC_OSTHREADNEW_5_EN                 ),
  TCD ( TC_osThreadNew_6,                 TC_OSTHREADNEW_6_EN                 ),
  TCD ( TC_osThreadNew_7,                 TC_OSTHREADNEW_7_EN                 ),
  TCD ( TC_osThreadGetName_1,             TC_OSTHREADGETNAME_1_EN             ),
  TCD ( TC_osThreadGetId_1,               TC_OSTHREADGETID_1_EN               ),
  TCD ( TC_osThreadGetState_1,            TC_OSTHREADGETSTATE_1_EN            ),
  TCD ( TC_osThreadGetState_2,            TC_OSTHREADGETSTATE_2_EN            ),
  TCD ( TC_osThreadGetState_3,            TC_OSTHREADGETSTATE_3_EN            ),
  TCD ( TC_osThreadSetPriority_1,         TC_OSTHREADSETPRIORITY_1_EN         ),
  TCD ( TC_osThreadSetPriority_2,         TC_OSTHREADSETPRIORITY_2_EN         ),
  TCD ( TC_osThreadGetPriority_1,         TC_OSTHREADGETPRIORITY_1_EN         ),
  TCD ( TC_osThreadYield_1,               TC_OSTHREADYIELD_1_EN               ),
  TCD ( TC_osThreadSuspend_1,             TC_OSTHREADSUSPEND_1_EN             ),
  TCD ( TC_osThreadResume_1,              TC_OSTHREADRESUME_1_EN              ),
  TCD ( TC_osThreadResume_2,              TC_OSTHREADRESUME_2_EN              ),
  TCD ( TC_osThreadDetach_1,              TC_OSTHREADDETACH_1_EN              ),
  TCD ( TC_osThreadDetach_2,              TC_OSTHREADDETACH_2_EN              ),
  TCD ( TC_osThreadJoin_1,                TC_OSTHREADJOIN_1_EN                ),
  TCD ( TC_osThreadJoin_2,                TC_OSTHREADJOIN_2_EN                ),
  TCD ( TC_osThreadJoin_3,                TC_OSTHREADJOIN_3_EN                ),
  TCD ( TC_osThreadExit_1,                TC_OSTHREADEXIT_1_EN                ),
  TCD ( TC_osThreadTerminate_1,           TC_OSTHREADTERMINATE_1_EN           ),
  TCD ( TC_osThreadGetStackSize_1,        TC_OSTHREADGETSTACKSIZE_1_EN        ),
  TCD ( TC_osThreadGetStackSpace_1,       TC_OSTHREADGETSTACKSPACE_1_EN       ),
  TCD ( TC_osThreadGetCount_1,            TC_OSTHREADGETCOUNT_1_EN            ),
  TCD ( TC_osThreadEnumerate_1,           TC_OSTHREADENUMERATE_1_EN           ),
  TCD ( TC_ThreadNew,                     TC_THREADNEW_EN                     ),
  TCD ( TC_ThreadMultiInstance,           TC_THREADMULTIINSTANCE_EN           ),
  TCD ( TC_ThreadTerminate,               TC_THREADTERMINATE_EN               ),
  TCD ( TC_ThreadRestart,                 TC_THREADRESTART_EN                 ),
  TCD ( TC_ThreadPriorityExec,            TC_THREADPRIORITYEXEC_EN            ),
  TCD ( TC_ThreadYield,                   TC_THREADYIELD_EN                   ),
  TCD ( TC_ThreadSuspendResume,           TC_THREADSUSPENDRESUME_EN           ),
  TCD ( TC_ThreadReturn,                  TC_THREADRETURN_EN                  ),
  TCD ( TC_ThreadAllocation,              TC_THREADALLOCATION_EN              ),
#endif
#if (TC_OSTHREADFLAGS_EN)
  TCD ( TC_ThreadFlagsMainThread,         TC_THREADFLAGSMAINTHREAD_EN         ),
  TCD ( TC_ThreadFlagsChildThread,        TC_THREADFLAGSCHILDTHREAD_EN        ),
  TCD ( TC_ThreadFlagsChildToParent,      TC_THREADFLAGSCHILDTOPARENT_EN      ),
  TCD ( TC_ThreadFlagsChildToChild,       TC_THREADFLAGSCHILDTOCHILD_EN       ),
  TCD ( TC_ThreadFlagsWaitTimeout,        TC_THREADFLAGSWAITTIMEOUT_EN        ),
  TCD ( TC_ThreadFlagsCheckTimeout,       TC_THREADFLAGSCHECKTIMEOUT_EN       ),
  TCD ( TC_ThreadFlagsParam,              TC_THREADFLAGSPARAM_EN              ),
  TCD ( TC_ThreadFlagsInterrupts,         TC_THREADFLAGSINTERRUPTS_EN         ),
#endif
#if (TC_OSDELAY_EN)
  TCD ( TC_GenWaitBasic,                  TC_GENWAITBASIC_EN                  ),
  TCD ( TC_GenWaitInterrupts,             TC_GENWAITINTERRUPTS_EN             ),
#endif
#if (TC_OSTIMER_EN)
  TCD ( TC_osTimerNew_1,                  TC_OSTIMERNEW_1_EN                  ),
  TCD ( TC_osTimerNew_2,                  TC_OSTIMERNEW_2_EN                  ),
  TCD ( TC_osTimerNew_3,                  TC_OSTIMERNEW_3_EN                  ),
  TCD ( TC_osTimerGetName_1,              TC_OSTIMERGETNAME_1_EN              ),
  TCD ( TC_osTimerStart_1,                TC_OSTIMERSTART_1_EN                ),
  TCD ( TC_osTimerStart_2,                TC_OSTIMERSTART_2_EN                ),
  TCD ( TC_osTimerStop_1,                 TC_OSTIMERSTOP_1_EN                 ),
  TCD ( TC_osTimerStop_2,                 TC_OSTIMERSTOP_2_EN                 ),
  TCD ( TC_osTimerIsRunning_1,            TC_OSTIMERISRUNNING_1_EN            ),
  TCD ( TC_osTimerDelete_1,               TC_OSTIMERDELETE_1_EN               ),
  TCD ( TC_TimerAllocation,               TC_TIMERALLOCATION_EN               ),
  TCD ( TC_TimerOneShot,                  TC_TIMERONESHOT_EN                  ),
  TCD ( TC_TimerPeriodic,                 TC_TIMERPERIODIC_EN                 ),
#endif
#if (TC_OSEVENTFLAGS_EN)
  TCD ( TC_osEventFlagsNew_1,             TC_OSEVENTFLAGSNEW_1_EN             ),
  TCD ( TC_osEventFlagsNew_2,             TC_OSEVENTFLAGSNEW_2_EN             ),
  TCD ( TC_osEventFlagsNew_3,             TC_OSEVENTFLAGSNEW_3_EN             ),
  TCD ( TC_osEventFlagsSet_1,             TC_OSEVENTFLAGSSET_1_EN             ),
  TCD ( TC_osEventFlagsClear_1,           TC_OSEVENTFLAGSCLEAR_1_EN           ),
  TCD ( TC_osEventFlagsGet_1,             TC_OSEVENTFLAGSGET_1_EN             ),
  TCD ( TC_osEventFlagsWait_1,            TC_OSEVENTFLAGSWAIT_1_EN            ),
  TCD ( TC_osEventFlagsDelete_1,          TC_OSEVENTFLAGSDELETE_1_EN          ),
  TCD ( TC_osEventFlagsGetName_1,         TC_OSEVENTFLAGSGETNAME_1_EN         ),
  TCD ( TC_EventFlagsAllocation,          TC_EVENTFLAGSALLOCATION_EN          ),
  TCD ( TC_EventFlagsInterThreads,        TC_EVENTFLAGSINTERTHREADS_EN        ),
  TCD ( TC_EventFlagsCheckTimeout,        TC_EVENTFLAGSCHECKTIMEOUT_EN        ),
  TCD ( TC_EventFlagsWaitTimeout,         TC_EVENTFLAGSWAITTIMEOUT_EN         ),
  TCD ( TC_EventFlagsDeleteWaiting,       TC_EVENTFLAGSDELETEWAITING_EN       ),
#endif
#if (TC_OSMUTEX_EN)
  TCD ( TC_osMutexNew_1,                  TC_OSMUTEXNEW_1_EN                  ),
  TCD ( TC_osMutexNew_2,                  TC_OSMUTEXNEW_2_EN                  ),
  TCD ( TC_osMutexNew_3,                  TC_OSMUTEXNEW_3_EN                  ),
  TCD ( TC_osMutexNew_4,                  TC_OSMUTEXNEW_4_EN                  ),
  TCD ( TC_osMutexNew_5,                  TC_OSMUTEXNEW_5_EN                  ),
  TCD ( TC_osMutexNew_6,                  TC_OSMUTEXNEW_6_EN                  ),
  TCD ( TC_osMutexGetName_1,              TC_OSMUTEXGETNAME_1_EN              ),
  TCD ( TC_osMutexAcquire_1,              TC_OSMUTEXACQUIRE_1_EN              ),
  TCD ( TC_osMutexAcquire_2,              TC_OSMUTEXACQUIRE_2_EN              ),
  TCD ( TC_osMutexRelease_1,              TC_OSMUTEXRELEASE_1_EN              ),
  TCD ( TC_osMutexGetOwner_1,             TC_OSMUTEXGETOWNER_1_EN             ),
  TCD ( TC_osMutexDelete_1,               TC_OSMUTEXDELETE_1_EN               ),
  TCD ( TC_MutexAllocation,               TC_MUTEXALLOCATION_EN               ),
  TCD ( TC_MutexCheckTimeout,             TC_MUTEXCHECKTIMEOUT_EN             ),
  TCD ( TC_MutexRobust,                   TC_MUTEXROBUST_EN                   ),
  TCD ( TC_MutexPrioInherit,              TC_MUTEXPRIOINHERIT_EN              ),
  TCD ( TC_MutexNestedAcquire,            TC_MUTEXNESTEDACQUIRE_EN            ),
  TCD ( TC_MutexPriorityInversion,        TC_MUTEXPRIORITYINVERSION_EN        ),
  TCD ( TC_MutexOwnership,                TC_MUTEXOWNERSHIP_EN                ),
#endif
#if (TC_OSSEMAPHORE_EN)
  TCD ( TC_osSemaphoreNew_1,              TC_OSSEMAPHORENEW_1_EN              ),
  TCD ( TC_osSemaphoreNew_2,              TC_OSSEMAPHORENEW_2_EN              ),
  TCD ( TC_osSemaphoreNew_3,              TC_OSSEMAPHORENEW_3_EN              ),
  TCD ( TC_osSemaphoreGetName_1,          TC_OSSEMAPHOREGETNAME_1_EN          ),
  TCD ( TC_osSemaphoreAcquire_1,          TC_OSSEMAPHOREACQUIRE_1_EN          ),
  TCD ( TC_osSemaphoreRelease_1,          TC_OSSEMAPHORERELEASE_1_EN          ),
  TCD ( TC_osSemaphoreGetCount_1,         TC_OSSEMAPHOREGETCOUNT_1_EN         ),
  TCD ( TC_osSemaphoreDelete_1,           TC_OSSEMAPHOREDELETE_1_EN           ),
  TCD ( TC_SemaphoreAllocation,           TC_SEMAPHOREALLOCATION_EN           ),
  TCD ( TC_SemaphoreCreateAndDelete,      TC_SEMAPHORECREATEANDDELETE_EN      ),
  TCD ( TC_SemaphoreObtainCounting,       TC_SEMAPHOREOBTAINCOUNTING_EN       ),
  TCD ( TC_SemaphoreObtainBinary,         TC_SEMAPHOREOBTAINBINARY_EN         ),
  TCD ( TC_SemaphoreWaitForBinary,        TC_SEMAPHOREWAITFORBINARY_EN        ),
  TCD ( TC_SemaphoreWaitForCounting,      TC_SEMAPHOREWAITFORCOUNTING_EN      ),
  TCD ( TC_SemaphoreZeroCount,            TC_SEMAPHOREZEROCOUNT_EN            ),
  TCD ( TC_SemaphoreWaitTimeout,          TC_SEMAPHOREWAITTIMEOUT_EN          ),
  TCD ( TC_SemaphoreCheckTimeout,         TC_SEMAPHORECHECKTIMEOUT_EN         ),
#endif
#if (TC_OSMEMORYPOOL_EN)
  TCD ( TC_osMemoryPoolNew_1,             TC_OSMEMORYPOOLNEW_1_EN             ),
  TCD ( TC_osMemoryPoolNew_2,             TC_OSMEMORYPOOLNEW_2_EN             ),
  TCD ( TC_osMemoryPoolNew_3,             TC_OSMEMORYPOOLNEW_3_EN             ),
  TCD ( TC_osMemoryPoolGetName_1,         TC_OSMEMORYPOOLGETNAME_1_EN         ),
  TCD ( TC_osMemoryPoolAlloc_1,           TC_OSMEMORYPOOLALLOC_1_EN           ),
  TCD ( TC_osMemoryPoolFree_1,            TC_OSMEMORYPOOLFREE_1_EN            ),
  TCD ( TC_osMemoryPoolGetCapacity_1,     TC_OSMEMORYPOOLGETCAPACITY_1_EN     ),
  TCD ( TC_osMemoryPoolGetBlockSize_1,    TC_OSMEMORYPOOLGETBLOCKSIZE_1_EN    ),
  TCD ( TC_osMemoryPoolGetCount_1,        TC_OSMEMORYPOOLGETCOUNT_1_EN        ),
  TCD ( TC_osMemoryPoolGetSpace_1,        TC_OSMEMORYPOOLGETSPACE_1_EN        ),
  TCD ( TC_osMemoryPoolDelete_1,          TC_OSMEMORYPOOLDELETE_1_EN          ),
  TCD ( TC_MemPoolAllocation,             TC_MEMPOOLALLOCATION_EN             ),
  TCD ( TC_MemPoolAllocAndFree,           TC_MEMPOOLALLOCANDFREE_EN           ),
  TCD ( TC_MemPoolAllocAndFreeComb,       TC_MEMPOOLALLOCANDFREECOMB_EN       ),
  TCD ( TC_MemPoolZeroInit,               TC_MEMPOOLZEROINIT_EN               ),
#endif
#if (TC_OSMESSAGEQUEUE_EN)
  TCD ( TC_osMessageQueueNew_1,           TC_OSMESSAGEQUEUENEW_1_EN           ),
  TCD ( TC_osMessageQueueNew_2,           TC_OSMESSAGEQUEUENEW_2_EN           ),
  TCD ( TC_osMessageQueueNew_3,           TC_OSMESSAGEQUEUENEW_3_EN           ),
  TCD ( TC_osMessageQueueGetName_1,       TC_OSMESSAGEQUEUEGETNAME_1_EN       ),
  TCD ( TC_osMessageQueuePut_1,           TC_OSMESSAGEQUEUEPUT_1_EN           ),
  TCD ( TC_osMessageQueuePut_2,           TC_OSMESSAGEQUEUEPUT_2_EN           ),
  TCD ( TC_osMessageQueueGet_1,           TC_OSMESSAGEQUEUEGET_1_EN           ),
  TCD ( TC_osMessageQueueGet_2,           TC_OSMESSAGEQUEUEGET_2_EN           ),
  TCD ( TC_osMessageQueueGetCapacity_1,   TC_OSMESSAGEQUEUEGETCAPACITY_1_EN   ),
  TCD ( TC_osMessageQueueGetMsgSize_1,    TC_OSMESSAGEQUEUEGETMSGSIZE_1_EN    ),
  TCD ( TC_osMessageQueueGetCount_1,      TC_OSMESSAGEQUEUEGETCOUNT_1_EN      ),
  TCD ( TC_osMessageQueueGetSpace_1,      TC_OSMESSAGEQUEUEGETSPACE_1_EN      ),
  TCD ( TC_osMessageQueueReset_1,         TC_OSMESSAGEQUEUERESET_1_EN         ),
  TCD ( TC_osMessageQueueDelete_1,        TC_OSMESSAGEQUEUEDELETE_1_EN        ),
  TCD ( TC_MsgQAllocation,                TC_MSGQALLOCATION_EN                ),
  TCD ( TC_MsgQBasic,                     TC_MSGQBASIC_EN                     ),
  TCD ( TC_MsgQWait,                      TC_MSGQWAIT_EN                      ),
  TCD ( TC_MsgQCheckTimeout,              TC_MSGQCHECKTIMEOUT_EN              ),
#endif
};

/*-----------------------------------------------------------------------------
 *      Test suite description
 *----------------------------------------------------------------------------*/
static TEST_SUITE ts = {
  __FILE__, __DATE__, __TIME__,
  "CMSIS-RTOS2 Test Suite",
  TS_Init,
  TS_Uninit,
  1,
  TC_List,
  sizeof(TC_List)/sizeof(TC_List[0])
};

/*-----------------------------------------------------------------------------
 *      CMSIS-RTOS2 Validation Entry
 *----------------------------------------------------------------------------*/
int cmsis_rv2 (void) {

  /* Initialize CMSIS-RTOS2 */
  osKernelInitialize();

  /* Create test framework main function as a thread */
  osThreadId_t id = osThreadNew((osThreadFunc_t)tf_main, &ts, &tf_main_attr);
  /* Start executing the test framework main function */
  osKernelStart();
  osThreadJoin(id);
  return (0);
}
