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
 
#include <iostream>
#include <thread>
#include <future>
#include <chrono>

// an example function that simulates a time-consuming calculation
int calculate_sum(int a, int b) {
    std::cout << "Start Computing " << a << " + " << b << "...\n";
    // simulate a time-consuming calculation (2 seconds)
    std::this_thread::sleep_for(std::chrono::seconds(2)); 
    std::cout << "Finish Computing " << a << " + " << b << "\n";
    return a + b;
}

int main() {
    std::cout << "[Main Thread] Starting async task...\n";

    // 1. use std::async start an task that will run calculate_sum(100, 200) in a new thread
    // std::launch::async strategy ensures the task will run asynchronously in a new thread
    std::future<int> result_future = std::async(std::launch::async, calculate_sum, 100, 200);

    // 2. while the child thread is computing, the main thread can do other things concurrently
    std::cout << "[Main Thread] Doing other things in parallel...\n";
    std::this_thread::sleep_for(std::chrono::milliseconds(500));
    std::cout << "[Main Thread] Finished other things, now waiting for the async result...\n";

    // 3. call get() to block and wait. If the child thread hasn't finished, the main thread will hang here; if it's done, it will directly get the value.
    int final_result = result_future.get();

    std::cout << "[Main Thread] Successfully got the async result: " << final_result << "\n";
    if (final_result == 300)
        std::cout << "Test Passed\n";
    else
        std::cout << "Test Failed\n";
    return 0;
}

extern "C" void __libc_init_array();
extern "C" void register_my_posix_tcb();
extern "C" void app_entry() { register_my_posix_tcb(); __libc_init_array(); main(); }

__attribute__((used, section(".bk_app_array")))
static void (*const __bk_app_entry)() = app_entry;
