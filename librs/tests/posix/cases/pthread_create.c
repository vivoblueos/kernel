/*
 * Copyright (c) 2026 vivo Mobile Communication Co., Ltd.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *       http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

#include <pthread.h>
#include <stddef.h>

#include "posix_case.h"

static volatile int worker_ran;

static void *worker(void *argument) {
  worker_ran = 1;
  return argument;
}

static int run(void) {
  pthread_t thread;
  void *result = NULL;
  int marker = 0;

  POSIX_ASSERT_EQ(pthread_create(&thread, NULL, worker, &marker), 0);
  POSIX_ASSERT_EQ(pthread_join(thread, &result), 0);
  POSIX_ASSERT_EQ(worker_ran, 1);
  POSIX_ASSERT(result == &marker);

  return POSIX_PASS;
}

POSIX_CASE("pthread_create", run);
