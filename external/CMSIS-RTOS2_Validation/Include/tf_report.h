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

#ifndef TF_REPORT_H__
#define TF_REPORT_H__

#include <stdint.h>

/*-----------------------------------------------------------------------------
 * Test Report Configuration
 *----------------------------------------------------------------------------*/

/*
  Print Output Format <0=> Plain Text <1=> XML
  Set the test results output format to plain text or XML
*/
#ifndef PRINT_XML_REPORT
#define PRINT_XML_REPORT            0
#endif

/*
  Buffer size for assertions results
  Set the buffer size for assertions results buffer
*/
#ifndef BUFFER_ASSERTIONS
#define BUFFER_ASSERTIONS           16
#endif

/*-----------------------------------------------------------------------------
 * Test report global definitions
 *----------------------------------------------------------------------------*/

/* Test case result definition */
typedef enum {
  PASSED = 0,
  WARNING,
  FAILED,
  NOT_EXECUTED
} TC_RES;

/* Assertion result info */
typedef struct {
  const char    *result;            /* Assertion result */
  const char    *module;            /* Module name      */
  uint32_t       line;              /* Assertion line   */
} AS_INFO;

/* Assertion statistics */
typedef struct {
  uint32_t passed;                  /* Assertions passed   */
  uint32_t failed;                  /* Assertions failed   */
  uint32_t warnings;                /* Assertions warnings */
} AS_STAT;

/* Test global statistics */
typedef struct {
  uint32_t  tests;                  /* Total test cases count         */
  uint32_t  executed;               /* Total test cases executed      */
  uint32_t  passed;                 /* Total test cases passed        */
  uint32_t  failed;                 /* Total test cases failed        */
  uint32_t  warnings;               /* Total test cases warnings      */
  AS_STAT   assertions;             /* Total assertions statistics    */
  AS_INFO   info[BUFFER_ASSERTIONS];/* Assertion failure/warning info */
} TEST_REPORT;

/* Test report interface */
int32_t TReport_Init     (void);
int32_t TReport_Open     (const char *title, const char *date, const char *time, const char *fn);
int32_t TReport_Close    (void);
int32_t TReport_TestOpen (uint32_t num, const char *fn);
int32_t TReport_TestAdd  (const char *fn, uint32_t ln, char *desc, TC_RES res);
int32_t TReport_TestClose(void);

#endif /* TF_REPORT_H__ */
