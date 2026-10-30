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

#include <stdarg.h>
#include <stdio.h>
#include <string.h>

#include "tf_main.h"
#include "tf_report.h"
#include "tf_assert.h"

/*
  Select test report print output
  0: Standard C library STDOUT
  1: Private printf implementation calling extern function stdout_putchar(ch)
*/
#ifndef TF_OUTPUT
#define TF_OUTPUT           1
#endif

/*
  Select print statement EOL style
  0: End Of Line: \n
  1: End Of Line: \r\n
*/
#ifndef TF_OUTPUT_CRLF
#define TF_OUTPUT_CRLF      1
#endif

/* Global Test Report structure */
TEST_REPORT TestReport;


/* Select test report print output */
#if (TF_OUTPUT == 0)
  /* Use standard C library functions */
  #define PRINT(x) print_stdio x
  #define FLUSH()  flush_stdio()
#elif (TF_OUTPUT == 1)
  /* Use static printf implementation and out_putchar() */
  extern void stdout_flush (void);
  #define PRINT(x) printf_lim x
  #define FLUSH()  stdout_flush()
#else
  #error "Unknown TF_OUTPUT setting."
#endif

/* Select print statement EOL style */
#if (TF_OUTPUT_CRLF == 0)
  /* End Of Line: \n */
  #define TF_EOL "\n"
#elif (TF_OUTPUT_CRLF == 1)
  /* End Of Line: \r\n */
  #define TF_EOL "\r\n"
#else
  #error "Invalid TF_OUTPUT_CRLF setting."
#endif

/* Temporary assert statistics */
static AS_STAT AssertStat;

#define TC_Asserts (&AssertStat)            /* Assert statistics: for the current Test Case */
#define TR_Asserts (&TestReport.assertions) /* Assert statistics: all Test Cases combined   */

static const char *Passed  = "PASSED";
static const char *Warning = "WARNING";
static const char *Failed  = "FAILED";
static const char *NotExe  = "NOT EXECUTED";

/* Printer function prototypes */
#if (TF_OUTPUT == 0)
static void print_stdio (const char *msg, ...);
static void flush_stdio (void);
#elif (TF_OUTPUT == 1)
extern int stdout_putchar (int ch);
static int out_putchar    (int ch);
static int printf_lim (const char *fmt, ...);
#endif

/* Test report function prototypes */
static const char *tr_Eval (void);
static const char *tc_Eval (void);

/*-----------------------------------------------------------------------------
 * Print Test Report: Start test case description
 *----------------------------------------------------------------------------*/
static void TR_Print_Open_TC (uint32_t num, const char *fn) {
#if (PRINT_XML_REPORT == 1)
  PRINT(("<tc>%s", TF_EOL));
  PRINT(("<no>%d</no>%s",     num, TF_EOL));
  PRINT(("<func>%s</func>%s", fn,  TF_EOL));
  PRINT(("<dbgi>%s", TF_EOL));
#else
  PRINT(("TEST %02d: %-32s ", num, fn));
#endif
  FLUSH();
}

/*-----------------------------------------------------------------------------
 * Print Test Report: Add test case debug information
 *----------------------------------------------------------------------------*/
static void TR_Print_WriteDebug (const char *fn, uint32_t ln, char *desc, const char *res) {
#if (PRINT_XML_REPORT == 1)
  PRINT(("<detail>%s", TF_EOL));
  PRINT(("<module>%s</module>%s", fn, TF_EOL));
  PRINT(("<line>%d</line>%s",     ln, TF_EOL));
  if (res != NULL) {
    PRINT(("<type>%s</type>%s",  res, TF_EOL));
  }
  if (desc != NULL) {
    PRINT(("<desc>%s</desc>%s", desc, TF_EOL));
  }
  PRINT(("</detail>%s", TF_EOL));
#else
  PRINT(("%s  %s (%d)", TF_EOL, fn, ln));
  if (res != NULL) {
    PRINT((" [%s]", res));
  }
  if (desc != NULL) {
    PRINT((" %s", desc));
  }
#endif
  FLUSH();
}
/*-----------------------------------------------------------------------------
 * Print Test Report: End test case description
 *----------------------------------------------------------------------------*/
static void TR_Print_Close_TC (const char *res) {
#if (PRINT_XML_REPORT == 1)
  PRINT(("</dbgi>%s", TF_EOL));
  PRINT(("<res>%s</res>%s", res, TF_EOL));
  PRINT(("</tc>%s", TF_EOL));
#else
  if ((res == Passed) || (res == NotExe))
    PRINT(("%s%s", res, TF_EOL));
  else
    PRINT(("%s", TF_EOL));
#endif
  FLUSH();
}

/*-----------------------------------------------------------------------------
 * Print Test Report: Output test report header
 *----------------------------------------------------------------------------*/
static void TR_Print_Open (const char *title, const char *date, const char *time, const char *fn) {
#if (PRINT_XML_REPORT == 1)
  PRINT(("<?xml version=\"1.0\"?>%s", TF_EOL));
  PRINT(("<?xml-stylesheet href=\"TR_Style.xsl\" type=\"text/xsl\" ?>%s", TF_EOL));
  PRINT(("<report>%s", TF_EOL));
  PRINT(("<test>%s", TF_EOL));
  PRINT(("<title>%s</title>%s", title, TF_EOL));
  PRINT(("<date>%s</date>%s",   date,  TF_EOL));
  PRINT(("<time>%s</time>%s",   time,  TF_EOL));
  PRINT(("<file>%s</file>%s",   fn,    TF_EOL));
  PRINT(("<test_cases>%s", TF_EOL));
#else
  (void)fn;
  PRINT(("%s   %s   %s %s%s", title, date, time, TF_EOL, TF_EOL));
#endif
  FLUSH();
}

/*-----------------------------------------------------------------------------
 * Print Test Report: Output test report summary
 *----------------------------------------------------------------------------*/
static void TR_Print_Close (void) {
#if (PRINT_XML_REPORT == 1)
  PRINT(("</test_cases>%s", TF_EOL));
  PRINT(("<summary>%s", TF_EOL));
  PRINT(("<tcnt>%d</tcnt>%s", TestReport.tests,    TF_EOL));
  PRINT(("<exec>%d</exec>%s", TestReport.executed, TF_EOL));
  PRINT(("<pass>%d</pass>%s", TestReport.passed,   TF_EOL));
  PRINT(("<fail>%d</fail>%s", TestReport.failed,   TF_EOL));
  PRINT(("<warn>%d</warn>%s", TestReport.warnings, TF_EOL));
  PRINT(("<tres>%s</tres>%s", tr_Eval(),            TF_EOL));
  PRINT(("</summary>%s", TF_EOL));
  PRINT(("</test>%s", TF_EOL));
  PRINT(("</report>%s", TF_EOL));
#else
  PRINT(("\nTest Summary: %d Tests, %d Executed, %d Passed, %d Failed, %d Warnings.%s",
         TestReport.tests,
         TestReport.executed,
         TestReport.passed,
         TestReport.failed,
         TestReport.warnings,
         TF_EOL));
  PRINT(("Test Result: %s%s", tr_Eval(), TF_EOL));
#endif
  FLUSH();
}

#if (TF_OUTPUT == 0)
/*-----------------------------------------------------------------------------
 *       print_stdio:  Print a message to the standard output
 *----------------------------------------------------------------------------*/
void print_stdio (const char *msg, ...) {
  va_list args;
  va_start(args, msg);
  vprintf(msg, args);
  va_end(args);
}

/*-----------------------------------------------------------------------------
 *       flush_stdio:  Flush the standard output
 *----------------------------------------------------------------------------*/
void flush_stdio (void) {
  fflush(stdout);
}

#elif (TF_OUTPUT == 1)

/**
  Reverse string str
*/
static void rev (char *str) {
  unsigned int i, j;
  char c;

  i = 0;
  j = strlen(str) - 1;

  while (i < j) {
    c = str[i];

    str[i] = str[j];
    str[j] = c;
    
    i++;
    j--;
  }
}

/**
  Convert integer n to string and store it to str buffer
*/
static char *itoa (int n, char *str, int base) {
  int s;
  int i;

  /* Limit to base 10 */
  if (base != 10) {
    return str;
  }

  /* Store sign */
  s = n;

  if (n < 0) {
    /* Convert to positive value */
    n = -n;
  }

  /* Convert to digits in reverse order */
  i = 0;

  do {
    str[i] = (char)(n % 10) + '0';
    i++;

    n = n / 10;
  }
  while (n > 0);
  
  /* Add sign */
  if (s < 0) {
    str[i++] = '-';
  }

  /* Terminate the string */
  str[i] = '\0';

  /* Reverse value before we return */
  rev(str);

  return str;
}

/**
  Convert string to integer, return pointer to first character after number in end
*/
static int atoi_ex (const char *str, const char **end) {
  int s;
  int i;
  int r;

  /* Init sign, result and index */
  s = 1;
  r = 0;
  i = 0;

  if (str[i] == '-') {
    /* Negative sign */
    s = -1;
    i++;
  }
  
  while ((str[i] >= '0') && (str[i] <= '9')) {
    r  = r * 10;
    r += str[i] - '0';

    i++;
  }

  /* Add correct sign */
  r *= s;
  
  *end = &str[i];

  return (r);
}


/*
  Limited vfprintf function

  Supports:
  - flags tags: %-
  - width field: supported, * (asterisk) not supported
  - format tags: %d, %s
*/
static int vprintf_lim (char const *fmt, va_list arg) {
  char  ch, *pch;
  char *a_string;
  int   a_int;
  int   len;
  unsigned int slen;
  int   m, p;

  /* Private vfprintf buffer */
  static char buf[512];

  len = 0;

  while (*fmt) {
    ch = *fmt++;

    if (ch == '%') {
      /* Process a format specifier */
      ch = *fmt++;
      m = 0;
      p = 0;

      /* Check flags */
      if (ch == '-') {
        /* %-xxX: left-justify within given width */
        m  = atoi_ex (fmt, &fmt);
        ch = *fmt++;
      }
      else if ((ch >= '0') && (ch <= '9')) {
        /* %0xX: prepend zero or space, ensure minimum num of characters to be printed */
        p = atoi_ex (fmt, &fmt);
        ch = *fmt++;
      }

      /* Print argument value */
      switch (ch) {
        case 'd': /* %d: print an integer */
          a_int = va_arg(arg, int);

          /* Convert value */
          itoa (a_int, buf, 10);

          slen = strlen(buf);

          /* Left-pad the number with spaces */
          p -= slen;
          while (p > 0) {
            out_putchar(' ');
            len++;
            p--;
          }

          /* Send to output */
          
          pch = buf;
          while (*pch) {
            out_putchar(*pch++);
          }
          len += slen;

          m -= slen;

          while (m > 0) {
            out_putchar(' ');
            len++;
            m--;
          }
          break;

        case 's': /* %s: print a string */
          a_string = va_arg(arg, char *);

          slen = strlen (a_string);

          /* Send to output */
          pch = a_string;
          while (*pch) {
            out_putchar(*pch++);
          }
          len += slen;

          m -= slen;

          while (m > 0) {
            out_putchar(' ');
            len++;
            m--;
          }
          break;

        default:
          /* Everything else is unsupported */
          out_putchar(ch);
          len++;
          break;
      }
    }
    else {
      /* Send directly to output */
      out_putchar(ch);
      len++;
    }
  }

  return len;
}



static int printf_lim (const char *fmt, ...) {
  va_list arg;
  int len;

  va_start(arg, fmt);
  len = vprintf_lim (fmt, arg);
  va_end(arg);

  return len;
}

static int out_putchar (int ch) {
  return stdout_putchar(ch);
}
#endif /* TF_OUTPUT */

/*-----------------------------------------------------------------------------
 * Strip path info
 *----------------------------------------------------------------------------*/
static const char *fn_strip (const char *fn) {
  const char *p;

  p = fn;

  while (*fn != '\0') {
    if ((*fn == '\\') || (*fn == '/')) {
      p = fn + 1;
    }
    fn++;
  }
  return (p);
}

/*-----------------------------------------------------------------------------
 * Evaluate test report results and return result string
 *----------------------------------------------------------------------------*/
static const char *tr_Eval (void) {

  if (TestReport.failed > 0) {
    /* Test fails if any test case failed */
    return (Failed);
  }
  else if (TestReport.warnings > 0) {
    /* Test warns if any test case warnings */
    return (Warning);
  }
  else if (TestReport.passed > 0) {
    /* Test passes if at least one test case passed */
    return (Passed);
  }
  else {
    /* No test cases were executed */
    return (NotExe);
  }
}


/*-----------------------------------------------------------------------------
 * Evaluate test case results and return result string
 *----------------------------------------------------------------------------*/
static const char *tc_Eval (void) {

  if (TC_Asserts->failed > 0) {
    /* Test case fails if any failed assertion recorded */
    return Failed;
  }
  else if (TC_Asserts->warnings > 0) {
    /* Test case warns if any warnings assertion recorded */
    return Warning;
  }
  else if (TC_Asserts->passed > 0) {
    /* Test case passes if at least one assertion passed */
    return Passed;
  }
  else {
    /* Assert was not invoked - nothing to evaluate */
    return NotExe;
  }
}

/*-----------------------------------------------------------------------------
 * Initialize Test Report
 *----------------------------------------------------------------------------*/
int32_t TReport_Init (void) {
  uint32_t i;

  /* Clear test results */
  TestReport.tests     = 0U;
  TestReport.executed  = 0U;
  TestReport.passed    = 0U;
  TestReport.failed    = 0U;
  TestReport.warnings  = 0U;

  /* Clear assert statistic */
  TR_Asserts->passed   = 0U;
  TR_Asserts->failed   = 0U;
  TR_Asserts->warnings = 0U;

  /* Clear debug information */
  for (i = 0U; i < BUFFER_ASSERTIONS; i++) {
    TestReport.info[i].result = NULL;
    TestReport.info[i].module = NULL;
    TestReport.info[i].line   = 0U;
  }

  return (0);
}

/*-----------------------------------------------------------------------------
 * Open test report
 *----------------------------------------------------------------------------*/
int32_t TReport_Open (const char *title, const char *date, const char *time, const char *fn) {

  TR_Print_Open (title, date, time, fn);

  return (0);
}

/*-----------------------------------------------------------------------------
 * Open test case
 *----------------------------------------------------------------------------*/
int32_t TReport_TestOpen (uint32_t num, const char *fn) {

  TC_Asserts->passed   = 0U;
  TC_Asserts->failed   = 0U;
  TC_Asserts->warnings = 0U;

  TR_Print_Open_TC (num, fn);

  return (0);
}

/*-----------------------------------------------------------------------------
 * Add test case assert result to the Test Report
 *----------------------------------------------------------------------------*/
int32_t TReport_TestAdd (const char *fn, uint32_t ln, char *desc, TC_RES res) {
#if (BUFFER_ASSERTIONS != 0)
  uint32_t n;
#endif
  const char *p;

  /* Update test report and current test case statistic */
  if (res == PASSED) {
    TC_Asserts->passed++;
    TR_Asserts->passed++;
  }
  else if (res == WARNING) {
    TC_Asserts->warnings++;
    TR_Asserts->warnings++;
  }
  else if (res == FAILED) {
    TC_Asserts->failed++;
    TR_Asserts->failed++;
  }
  else {
    /* Not Executed */
  }

  /* Add debug info if assertion passed with warnings or failed */
  if ((res == WARNING) || (res == FAILED)) {
    /* Strip path information from the file name */
    fn = fn_strip (fn);

    /* Get result string */
    p = tc_Eval();

    #if (BUFFER_ASSERTIONS != 0)
    /* Add failures and warnings info into memory buffer */
    n = TR_Asserts->failed + TR_Asserts->warnings - 1U;

    if (n < BUFFER_ASSERTIONS) {
      TestReport.info[n].module = fn;
      TestReport.info[n].line   = ln;
      TestReport.info[n].result = p;
    }
    #endif

    TR_Print_WriteDebug (fn, ln, desc, p);
  }

  return (0);
}

/*-----------------------------------------------------------------------------
 * Close test case
 *----------------------------------------------------------------------------*/
int32_t TReport_TestClose (void) {
  const char *res;

  /* Increment test report test statistic */
  TestReport.tests++;
  TestReport.executed++;

  res = tc_Eval();

  if (res == Passed) {
    TestReport.passed++;
  }
  else if (res == Warning) {
    TestReport.warnings++;
  }
  else if (res == Failed) {
    TestReport.failed++;
  }
  else {
    /* Not executed */
    TestReport.executed--;
  }

  TR_Print_Close_TC (res);

  return (0);
}


/*-----------------------------------------------------------------------------
 * Close test report
 *----------------------------------------------------------------------------*/
int32_t TReport_Close (void) {

  TR_Print_Close();

  return (0);
}

/*-----------------------------------------------------------------------------
 * Assert true
 *----------------------------------------------------------------------------*/
uint32_t __assert_true (const char *fn, uint32_t ln, uint32_t cond) {
  TC_RES res;

  if (cond == 0U) {
    /* Condition is not true, test failed */
    res = FAILED;
  } else {
    /* Condition is true, test passed */
    res = PASSED;
  }

  TReport_TestAdd (fn, ln, NULL, res);

  return (cond);
}
