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
#include <stdio.h>

class Counter {
public:
  Counter() : count_(0) {}
  void increment() { count_++; }
  int get() const { return count_; }
private:
  int count_;
};

static void *thread_func(void *arg) {
  Counter *c = static_cast<Counter *>(arg);
  c->increment();
  return NULL;
}

int main() {
  Counter c;
  pthread_t tid;

  c.increment();
  if (pthread_create(&tid, NULL, thread_func, &c) != 0) {
    printf("Test failed\n");
    return -1;
  }
  if (pthread_join(tid, NULL) != 0) {
    printf("Test failed\n");
    return -1;
  }
  c.increment();
  if (c.get() == 3) {
    printf("Test passed\n");
    return 0;
  }
  printf("Test failed\n");
  return -1;
}

extern "C" void app_entry() { main(); }

__attribute__((used, section(".bk_app_array")))
static void (*const __bk_app_entry)() = app_entry;
