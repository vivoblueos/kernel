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

#include "tf_main.h"
#include "tf_report.h"

/*=======0=========1=========2=========3=========4=========5=========6=========7=========8=========9=========0=========1====*/
/**
\defgroup framework_funcs Test Framework Functions
\brief Functions in the Test Framework software component
\details

@{
*/

/**
\brief This is the entry point of the test framework.
\details
Program flow:
  -# Test suite Init() callback function is called if function is provided
  -# Test report statistics is initialized
  -# Test report headers are written to the standard output
  -# All defined test cases are executed:
      - Test case statistics is initialized
      - Test case report header is written to the standard output
      - Test case is executed
      - Test case results are written to the standard output
      - Test case is closed
  -# Test report footer is written to the standard output
  -# Test suite Uninit() callback function is called if function is provided
  -# Function returns
*/
void tf_main (TEST_SUITE *ts) {
  const char *fn;
  uint32_t tc, no;

  /* Init test suite */
  if (ts->Init != NULL) {
    ts->Init();
  }

  TReport_Init ();                        /* Init test report                 */
  TReport_Open (ts->ReportTitle,          /* Write test report title          */
                ts->Date,                 /* Write compilation date           */
                ts->Time,                 /* Write compilation time           */
                ts->FileName);            /* Write module file name           */

  /* Execute all test cases */
  for (tc = 0; tc < ts->NumOfTC; tc++) {
    no = ts->TCBaseNum+tc;                /* Test case number                 */
    fn = ts->TC[tc].TFName;               /* Test function name string        */
    TReport_TestOpen (no, fn);            /* Open test case                   */
    if (ts->TC[tc].en) 
      ts->TC[tc].TestFunc();              /* Execute test case if enabled     */
    TReport_TestClose ();                 /* Close test case                  */
  }
  TReport_Close ();                       /* Close test report                */

  if (ts->Uninit != NULL) {               /* Uninit test suite                */
    ts->Uninit();
  }
}


/**
@}
*/ 
// end of group framework_funcs
