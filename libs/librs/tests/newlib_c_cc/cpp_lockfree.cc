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

#include <atomic>
#include <cstddef>
#include <iostream>
#include <thread>

template <typename T, std::size_t N>
class LockFreeQueue {
    static_assert((N & (N -1)) == 0, "N must be a power of 2");
    static_assert(N >= 2, "N must be at least 2");
public:
    LockFreeQueue() : head_(0), tail_(0) {};
    bool enqueue(const T& item) {
        std::size_t current_tail = tail_.load(std::memory_order_relaxed);
        std::size_t current_head = head_.load(std::memory_order_acquire);
        if (current_tail - current_head == N) {
            return false; // Queue is full
        }
        buffer_[current_tail & (N - 1)] = item;
        tail_.store(current_tail + 1, std::memory_order_release);
        return true;
    }
    bool dequeue(T& item) {
        std::size_t current_head = head_.load(std::memory_order_relaxed);
        std::size_t current_tail = tail_.load(std::memory_order_acquire);
        if (current_head == current_tail) {
            return false; // Queue is empty
        }
        item = buffer_[current_head & (N - 1)];
        head_.store(current_head + 1, std::memory_order_release);
        return true;
    }
private:
    T buffer_[N];
    std::atomic<std::size_t> head_;
    std::atomic<std::size_t> tail_;
};

LockFreeQueue<int, 1024> queue;
void producer() {
    for (int i = 0; i < 1000; ++i) {
        while (!queue.enqueue(i)) {
            std::this_thread::yield(); // Wait if the queue is full
        }
    }
}
void consumer() {
    int item;
    for (int i = 0; i < 1000; ++i) {
        while (!queue.dequeue(item)) {
            std::this_thread::yield(); // Wait if the queue is empty
        }
        if (item != i) {
            std::cout << "Test Failed, Expected: " << i << ", Got: " << item << std::endl;
            return;
        }
    }
    std::cout << "Test Passed, All items dequeued in order." << std::endl;
}
int main() {
    std::thread prod(producer);
    std::thread cons(consumer);
    prod.join();
    cons.join();
    return 0;
}

extern "C" void __libc_init_array();
extern "C" void register_my_posix_tcb();
extern "C" void app_entry() { register_my_posix_tcb(); __libc_init_array(); main(); }

__attribute__((used, section(".bk_app_array")))
static void (*const __bk_app_entry)() = app_entry;