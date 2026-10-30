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
#include <mutex>
#include <condition_variable>
#include <queue>

std::mutex mtx;
std::condition_variable cv;
std::queue<int> data_queue;
bool done = false;

void producer() {
    for (int i = 1; i <= 5; ++i) {
        std::unique_lock<std::mutex> lock(mtx);
        data_queue.push(i);
        std::cout << "[Producer] Pushed: " << i << std::endl;
        cv.notify_one();
        lock.unlock();
        std::this_thread::sleep_for(std::chrono::milliseconds(50));
    }
    std::unique_lock<std::mutex> lock(mtx);
    done = true;
    cv.notify_all();
}

void consumer() {
    while (true) {
        std::unique_lock<std::mutex> lock(mtx);
        cv.wait(lock, []{ return !data_queue.empty() || done; });
        while (!data_queue.empty()) {
            std::cout << "[Consumer] Got: " << data_queue.front() << std::endl;
            data_queue.pop();
        }
        if (done) break;
    }
}

int main() {
    std::thread t1(producer);
    std::thread t2(consumer);
    t1.join();
    t2.join();
    std::cout << "Test passed\n";
    return 0;
}

extern "C" void __libc_init_array();
extern "C" void register_my_posix_tcb();
extern "C" void app_entry() { register_my_posix_tcb(); __libc_init_array(); main(); }

__attribute__((used, section(".bk_app_array")))
static void (*const __bk_app_entry)() = app_entry;

