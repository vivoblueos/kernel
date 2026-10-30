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
 
#include <stdio.h>
#include <vector>
#include <thread>
#include <chrono>

int main() {
  // Test: basic C++11 thread support
  std::vector<std::thread> threads;
  for (int i = 0; i < 4; i++) {
    threads.emplace_back([]() {
      // Just sleep for a bit to test thread creation and teardown
      std::this_thread::sleep_for(std::chrono::milliseconds(100));
    });
  }
  for (auto &t : threads) {
    t.join();
  }
  printf("Test passed\n");

  return 0;
}

extern "C" void app_entry() { main(); }

__attribute__((used, section(".bk_app_array")))
static void (*const __bk_app_entry)() = app_entry;