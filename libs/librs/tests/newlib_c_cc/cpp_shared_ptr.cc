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

#include <memory>
#include <pthread.h>
#include <stdio.h>

struct SharedData {
  int value;
  static int live_count;
  SharedData(int v) : value(v) { live_count++; }
  ~SharedData() { live_count--; }
};

int SharedData::live_count = 0;

static void *thread_func(void *arg) {
  std::shared_ptr<SharedData> *shared_ptr_ref =
      static_cast<std::shared_ptr<SharedData> *>(arg);

  // Each thread creates a copy (increments refcount), modifies, then drops it
  std::shared_ptr<SharedData> local_copy = *shared_ptr_ref;
  local_copy->value += 1;

  // Create and immediately destroy a shared_ptr to test construct/destruct under concurrency
  {
    std::shared_ptr<SharedData> temp = std::make_shared<SharedData>(100);
    temp->value += 1;
  }

  return NULL;
}

int main() {
  // Test: shared_ptr refcount is correct across multi-threaded construct/destruct
  auto ptr = std::make_shared<SharedData>(0);
  if (SharedData::live_count != 1) {
    printf("Test failed: initial live_count=%d, expected 1\n",
           SharedData::live_count);
    return -1;
  }

  pthread_t tids[4];
  for (int i = 0; i < 4; i++) {
    if (pthread_create(&tids[i], NULL, thread_func, &ptr) != 0) {
      printf("Test failed: pthread_create %d\n", i);
      return -1;
    }
  }

  for (int i = 0; i < 4; i++) {
    if (pthread_join(tids[i], NULL) != 0) {
      printf("Test failed: pthread_join %d\n", i);
      return -1;
    }
  }

  // All thread-local shared_ptrs destroyed; only the original ptr remains
  if (SharedData::live_count != 1) {
    printf("Test failed: final live_count=%d, expected 1\n",
           SharedData::live_count);
    return -1;
  }

  // 4 threads each incremented value by 1
  if (ptr->value != 4) {
    printf("Test failed: final value=%d, expected 4\n", ptr->value);
    return -1;
  }

  ptr.reset();
  if (SharedData::live_count != 0) {
    printf("Test failed: after reset live_count=%d, expected 0\n",
           SharedData::live_count);
    return -1;
  }

  printf("Test passed\n");
  return 0;
}

extern "C" void app_entry() { main(); }

__attribute__((used, section(".bk_app_array")))
static void (*const __bk_app_entry)() = app_entry;
