/* --------------------------------------------------------------------------
 * Copyright (c) 2013-2024 Arm Limited. All rights reserved.
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
 *
 * --------------------------------------------------------------------------
 *
 * $Revision:   V10.6.0
 *
 * Project:     CMSIS-FreeRTOS
 * Title:       FreeRTOS configuration definitions
 *
 * --------------------------------------------------------------------------*/

#ifndef FREERTOS_CONFIG_H
#define FREERTOS_CONFIG_H

/*-----------------------------------------------------------
 * Application specific definitions.
 *
 * These definitions should be adjusted for your particular hardware and
 * application requirements.
 *
 * THESE PARAMETERS ARE DESCRIBED WITHIN THE 'CONFIGURATION' SECTION OF THE
 * FreeRTOS API DOCUMENTATION AVAILABLE ON THE FreeRTOS.org WEB SITE.
 *
 * See http://www.freertos.org/a00110.html
 *----------------------------------------------------------*/

#if (defined(__ARMCC_VERSION) || defined(__GNUC__) || defined(__ICCARM__))
#include <stdint.h>

#include "RTE_Components.h"
#include CMSIS_device_header
#endif

//-------- <<< Use Configuration Wizard in Context Menu >>> --------------------

//  <o>Minimal stack size [words] <0-65535>
//  <i> Stack for idle task and default task stack in words.
//  <i> Default: 128
#define configMINIMAL_STACK_SIZE                  ((uint16_t)(128))

//  <o>Total heap size [bytes] <0-0xFFFFFFFF>
//  <i> Heap memory size in bytes.
//  <i> Default: 8192
#define configTOTAL_HEAP_SIZE                     ((size_t)8192)

//  <o>Kernel tick frequency [Hz] <0-0xFFFFFFFF>
//  <i> Kernel tick rate in Hz.
//  <i> Default: 1000
#define configTICK_RATE_HZ                        ((TickType_t)1000)

//  <o>Timer task stack depth [words] <0-65535>
//  <i> Stack for timer task in words.
//  <i> Default: 80
#define configTIMER_TASK_STACK_DEPTH              80

//  <o>Timer task priority <0-56>
//  <i> Timer task priority.
//  <i> Default: 40 (High)
#define configTIMER_TASK_PRIORITY                 40

//  <o>Timer queue length <0-1024>
//  <i> Timer command queue length.
//  <i> Default: 5
#define configTIMER_QUEUE_LENGTH                  5

//  <o>Preemption interrupt priority
//  <i> Maximum priority of interrupts that are safe to call FreeRTOS API.
//  <i> Default: 128
#define configMAX_SYSCALL_INTERRUPT_PRIORITY      128

//  <q>Use time slicing
//  <i> Enable setting to use timeslicing.
//  <i> Default: 1
#define configUSE_TIME_SLICING                    1

//  <q>Use tickless idle
//  <i> Enable low power tickless mode to stop the periodic tick interrupt during idle periods or
//  <i> disable it to keep the tick interrupt running at all times.
//  <i> Default: 0
#define configUSE_TICKLESS_IDLE                   0

//  <q>Idle should yield
//  <i> Control Yield behaviour of the idle task.
//  <i> Default: 1
#define configIDLE_SHOULD_YIELD                   1

//  <o>Check for stack overflow
//    <0=>Disable <1=>Method one <2=>Method two
//  <i> Enable or disable stack overflow checking.
//  <i> Callback function vApplicationStackOverflowHook implementation is required when stack checking is enabled.
//  <i> Default: 0
#define configCHECK_FOR_STACK_OVERFLOW            2

//  <q>Use idle hook
//  <i> Enable callback function call on each idle task iteration.
//  <i> Callback function vApplicationIdleHook implementation is required when idle hook is enabled.
//  <i> Default: 0
#define configUSE_IDLE_HOOK                       0

//  <q>Use tick hook
//  <i> Enable callback function call during each tick interrupt.
//  <i> Callback function vApplicationTickHook implementation is required when tick hook is enabled.
//  <i> Default: 0
#define configUSE_TICK_HOOK                       0

//  <q>Use deamon task startup hook
//  <i> Enable callback function call when timer service starts.
//  <i> Callback function vApplicationDaemonTaskStartupHook implementation is required when deamon task startup hook is enabled.
//  <i> Default: 0
#define configUSE_DAEMON_TASK_STARTUP_HOOK        0

//  <q>Use malloc failed hook
//  <i> Enable callback function call when out of dynamic memory.
//  <i> Callback function vApplicationMallocFailedHook implementation is required when malloc failed hook is enabled.
//  <i> Default: 0
#define configUSE_MALLOC_FAILED_HOOK              0

//  <o>Queue registry size
//  <i> Define maximum number of queue objects registered for debug purposes.
//  <i> The queue registry is used by kernel aware debuggers to locate queue and semaphore structures and display associated text names.
//  <i> Default: 0
#define configQUEUE_REGISTRY_SIZE                 0

// <h>Event Recorder Configuration
// <i> Initialize and setup Event Recorder level filtering.
// <i> Settings have no effect when Event Recorder is not present.

//  <q>Initialize Event Recorder
//  <i> Initialize Event Recorder before FreeRTOS kernel start.
//  <i> Default: 1
#define configEVR_INITIALIZE                      1

//  <e>Setup recording level filter
//  <i> Enable configuration of FreeRTOS events recording level
//  <i> Default: 1
#define configEVR_SETUP_LEVEL                     1

//  <o>Tasks functions
//  <i> Define event recording level bitmask for events generated from Tasks functions.
//  <i> Default: 0x05
//    <0x00=>Off <0x01=>Errors <0x03=>Errors + API <0x05=>Errors + Operation <0x07=>Errors + API + Operation <0x0F=>All
#define configEVR_LEVEL_TASKS                     0x05

//  <o>Queue functions
//  <i> Define event recording level bitmask for events generated from Queue functions.
//  <i> Default: 0x05
//    <0x00=>Off <0x01=>Errors <0x03=>Errors + API <0x05=>Errors + Operation <0x07=>Errors + API + Operation <0x0F=>All
#define configEVR_LEVEL_QUEUE                     0x05

//  <o>Timer functions
//  <i> Define event recording level bitmask for events generated from Timer functions.
//  <i> Default: 0x05
//    <0x00=>Off <0x01=>Errors <0x03=>Errors + API <0x05=>Errors + Operation <0x07=>Errors + API + Operation <0x0F=>All
#define configEVR_LEVEL_TIMERS                    0x05

//  <o>Event Groups functions
//  <i> Define event recording level bitmask for events generated from Event Groups functions.
//  <i> Default: 0x05
//    <0x00=>Off <0x01=>Errors <0x03=>Errors + API <0x05=>Errors + Operation <0x07=>Errors + API + Operation <0x0F=>All
#define configEVR_LEVEL_EVENTGROUPS               0x05

//  <o>Heap functions
//  <i> Define event recording level bitmask for events generated from Heap functions.
//  <i> Default: 0x05
//    <0x00=>Off <0x01=>Errors <0x03=>Errors + API <0x05=>Errors + Operation <0x07=>Errors + API + Operation <0x0F=>All
#define configEVR_LEVEL_HEAP                      0x05

//  <o>Stream Buffer functions
//  <i> Define event recording level bitmask for events generated from Stream Buffer functions.
//  <i> Default: 0x05
//    <0x00=>Off <0x01=>Errors <0x03=>Errors + API <0x05=>Errors + Operation <0x07=>Errors + API + Operation <0x0F=>All
#define configEVR_LEVEL_STREAMBUFFER              0x05
//  </e>
// </h>

// <h>Memory Allocation Configuration
// <i> Enable and configure memory allocation specific features.
// <i> To configure FreeRTOS heap size use configTOTAL_HEAP_SIZE.

//  <q> Support static memory allocation
//  <i> Enable or disable static memory allocation.
//  <i> When enabled RTOS objects can be created using application provided RAM.
//  <i> Default: 1
#define configSUPPORT_STATIC_ALLOCATION           1

//  <q> Support dynamic memory allocation
//  <i> Enable or disable dynamic memory allocation.
//  <i> When enabled RTOS objects can be created using RAM automatically allocated from the FreeRTOS heap.
//  <i> Default: 1
#define configSUPPORT_DYNAMIC_ALLOCATION          1

//  <q>Use kernel provided static memory
//  <i> When enabled FreeRTOS kernel provides static memory for Idle and Timer tasks.
//  <i> Otherwise user shall provide implementation of:
//  <i> - vApplicationGetIdleTaskMemory and vApplicationGetTimerTaskMemory
//  <i> - vApplicationGetPassiveIdleTaskMemory (when kernel uses SMP)
//  <i> Default: 1
#define configKERNEL_PROVIDED_STATIC_MEMORY       1

//  <q>Use application allocated heap
//  <i> Global heap buffer must be provided externally when using application allocated heap.
//  <i> The buffer must be declared as: uint8_t ucHeap[ configTOTAL_HEAP_SIZE ].
//  <i> Default: 0
#define configAPPLICATION_ALLOCATED_HEAP          0

//  <q>Use separate heap for stack allocation
//  <i> Enable or disable stack allocation for any task from a separate heap.
//  <i> Thread-safe implementation of pvPortMallocStack and vPortFreeStack is required when using separate heap.
//  <i> Default: 0
#define configSTACK_ALLOCATION_FROM_SEPARATE_HEAP 0

//  <q>Use heap protector
//  <i> Enable or disable bounds checking and obfuscation to heap block pointers.
//  <i> This setting only applies to Heap_4 and Heap_5.
//  <i> Default: 0
#define configENABLE_HEAP_PROTECTOR               0
// </h>

// <h>Port Specific Configuration
// <i> Enable and configure port specific features.
// <i> Check FreeRTOS documentation for definitions that apply for the used port.

//  <q>Use Floating Point Unit
//  <i> Using Floating Point Unit (FPU) affects context handling.
//  <i> Enable FPU when application uses floating point operations.
//  <i> This setting is only relevant on ARMv8-M ports.
//  <i> Default: 1
#define configENABLE_FPU                          1

//  <q>Use M-Profile Vector Extension
//  <i> Using M-Profile Vector Extension (MVE) affects context handling.
//  <i> Enable MVE when application uses signal processing and ML algorithms.
//  <i> This setting is only relevant on ARMv8-M ports.
//  <i> Default: 0
#define configENABLE_MVE                          0

//  <q>Use Memory Protection Unit
//  <i> Using Memory Protection Unit (MPU) requires detailed memory map definition.
//  <i> This setting is only relevant on ARMv8-M MPU enabled ports.
//  <i> Default: 0
#define configENABLE_MPU                          0

//  <q>Use TrustZone Secure Side Only
//  <i> This settings prevents FreeRTOS contex switch to Non-Secure side.
//  <i> Enable this setting when FreeRTOS runs on the Secure side only.
//  <i> This setting is only relevant on ARMv8-M ports.
//  <i> Default: 0
#define configRUN_FREERTOS_SECURE_ONLY            0

//  <q>Use TrustZone Security Extension
//  <i> Using TrustZone affects context handling.
//  <i> Enable TrustZone when FreeRTOS runs on the Non-Secure side and calls functions from the Secure side.
//  <i> This setting is only relevant on ARMv8-M ports.
//  <i> Default: 1
#define configENABLE_TRUSTZONE                    1

//  <o>Minimal secure stack size [words] <0-65535>
//  <i> Stack for idle task Secure side context in words.
//  <i> This setting is only relevant on ARMv8-M ports when TrustZone extension is enabled.
//  <i> Default: 128
#define configMINIMAL_SECURE_STACK_SIZE           ((uint32_t)128)

//  <h>Interrupt Controller Configuration
//  <i> Configure Arm Generic Interrupt Controller (GIC) interrupt controller specific settings.
//  <i> Settings related to interrupt controller are relevant only on ARMv7-A ports.

//   <o>Interrupt controller base address
//   <i> Must be set to the base address of the interrupt controller peripheral.
//   <i> Default: 0x2C000000
#define configINTERRUPT_CONTROLLER_BASE_ADDRESS   0x2C000000UL

//   <o>Interrupt controller CPU interface offset
//   <i> Must be set to the offset from interrupt controller base address at which the CPU interface starts.
//   <i> Default: 0x1000
#define configINTERRUPT_CONTROLLER_CPU_INTERFACE_OFFSET 0x00001000UL

//   <o>Interrupt controller unique priorities
//   <i> The number of unique priorities that can be specified in the interrupt controller peripheral.
//   <i> Default: 32
#define configUNIQUE_INTERRUPT_PRIORITIES         32
//  </h>
// </h>

// <h>Symmetric Multiprocessing Configuration
// <i> Enable and configure FreeRTOS for Symmetric Multiprocessing (SMP).

//  <o>Number of processor cores
//  <i> Sets the number of available processor cores.
//  <i> Default: 1
#define configNUMBER_OF_CORES                     1

//  <q>Use processor core affinity
//  <i> Enables the control for task to run on specific processor cores.
//  <i> Task that has no processor affinity set may run on any available core.
//  <i> Default: 0
#define configUSE_CORE_AFFINITY                   0

//  <q>Use passive idle hook
//  <i> Enable callback function call on each idle task iteration.
//  <i> Callback function vApplicationPassiveIdleHook implementation is required when idle hook is enabled.
//  <i> Default: 0
#define configUSE_PASSIVE_IDLE_HOOK               0
// </h>

//------------- <<< end of configuration section >>> ---------------------------

/* Defines needed by FreeRTOS to implement CMSIS RTOS2 API. Do not change! */
#define configCPU_CLOCK_HZ                        (SystemCoreClock)
#define configUSE_PREEMPTION                      1
#define configUSE_TIMERS                          1
#define configUSE_MUTEXES                         1
#define configUSE_RECURSIVE_MUTEXES               1
#define configUSE_COUNTING_SEMAPHORES             1
#define configUSE_TASK_NOTIFICATIONS              1
#define configUSE_TRACE_FACILITY                  1
#define configUSE_16_BIT_TICKS                    0
#define configUSE_PORT_OPTIMISED_TASK_SELECTION   0
#define configMAX_PRIORITIES                      56
#define configKERNEL_INTERRUPT_PRIORITY           255

/* Defines that include FreeRTOS functions which implement CMSIS RTOS2 API. Do not change! */
#define INCLUDE_xEventGroupSetBitsFromISR         1
#define INCLUDE_xSemaphoreGetMutexHolder          1
#define INCLUDE_vTaskDelay                        1
#define INCLUDE_xTaskDelayUntil                   1
#define INCLUDE_vTaskDelete                       1
#define INCLUDE_xTaskGetCurrentTaskHandle         1
#define INCLUDE_xTaskGetSchedulerState            1
#define INCLUDE_uxTaskGetStackHighWaterMark       1
#define INCLUDE_uxTaskPriorityGet                 1
#define INCLUDE_vTaskPrioritySet                  1
#define INCLUDE_eTaskGetState                     1
#define INCLUDE_vTaskSuspend                      1
#define INCLUDE_xTaskAbortDelay                   1
#define INCLUDE_xTimerPendFunctionCall            1

#if (__ARM_ARCH_7A__ == 1U)
  /* Cortex-A specifics */
  #include "os_tick.h"

  /* Maximum API call interrupt priority:
     - Interrupts assigned a priority at or below this priority can call interrupt safe FreeRTOS API function, and will nest.
     - Interrupts assigned a priority above this priority will not be effected by RTOS critical sections, and will nest,
       but cannot call any FreeRTOS API functions.
     - Use configMAX_SYSCALL_INTERRUPT_PRIORITY to set this define as they are essentially the same.
  */
  #define configMAX_API_CALL_INTERRUPT_PRIORITY   configMAX_SYSCALL_INTERRUPT_PRIORITY

  /* Map the FreeRTOS port timer configuration functions to their implementations */
  #define configSETUP_TICK_INTERRUPT()                         \
    OS_Tick_Setup (configTICK_RATE_HZ, FreeRTOS_Tick_Handler); \
    OS_Tick_Enable();

  #define configCLEAR_TICK_INTERRUPT()                         \
    OS_Tick_AcknowledgeIRQ()
#else
  /* Cortex-M specifics */
  /* Map the FreeRTOS port interrupt handlers to their CMSIS standard names. */
  #define xPortPendSVHandler                      PendSV_Handler
  #define vPortSVCHandler                         SVC_Handler

  /* Ensure Cortex-M port compatibility. */
  #define SysTick_Handler                         xPortSysTickHandler

  #if (defined(__ARMCC_VERSION) || defined(__GNUC__) || defined(__ICCARM__))
  /* Include debug event definitions */
  #include "freertos_evr.h"
  #endif
#endif

#endif /* FREERTOS_CONFIG_H */
