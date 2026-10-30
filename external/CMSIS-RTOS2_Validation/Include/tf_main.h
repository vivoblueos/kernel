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

#ifndef TF_MAIN_H__
#define TF_MAIN_H__

#include <stddef.h>
#include <stdint.h>
#include "tf_assert.h"
#include "tf_report.h"

/*-----------------------------------------------------------------------------
 * Test framework global definitions
 *----------------------------------------------------------------------------*/

/* Test case definition macro                                                 */
#define TCD(x, y) {x, #x, y}

/* Test case description structure                                            */
typedef struct __TestCase {
  void (*TestFunc)(void);             /* Test function                        */
  const char *TFName;                 /* Test function name string            */
  int32_t en;                         /* Test function enabled                */
} TEST_CASE;

/* Test suite description structure                                           */
typedef struct __TestSuite {
  const char *FileName;               /* Test module file name                */
  const char *Date;                   /* Compilation date                     */
  const char *Time;                   /* Compilation time                     */
  const char *ReportTitle;            /* Title or name of module under test   */
  void (*Init)(void);                 /* Test suite init callback function    */
  void (*Uninit)(void);               /* Test suite uninit callback function  */

  uint32_t TCBaseNum;                 /* Base number for test case numbering  */
  const TEST_CASE *TC;                /* Array of test cases                  */
  uint32_t NumOfTC;                   /* Number of test cases (sz of TC array)*/

} TEST_SUITE;

/* Defined in user test module                                                */
extern void tf_main (TEST_SUITE *ts);

/* Test Report: statistic, debug information in RAM                           */
extern TEST_REPORT  TestReport;

/**
  ASSERT_TRUE:
  - test passes if condition is true
  - test fails if condition is false

\param[in]  cond          condition to evaluate
\return     Test result (true if test passed, false if test failed)
*/
#define ASSERT_TRUE(cond)             __assert_true (__FILE__, __LINE__, cond)

#endif /* TF_MAIN_H__ */
