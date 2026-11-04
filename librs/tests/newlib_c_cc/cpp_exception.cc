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
#include <stdexcept>

void depth_3() {
    throw std::runtime_error("Trigger Exception");
}
void depth_2() { depth_3(); }
void depth_1() { depth_2(); }

int main() {
    try {
        depth_1();
    } catch (const std::runtime_error& e) {
        std::cout << "Test Passed, Exception caught safely: " << e.what() << std::endl;
    } catch (...) {
        std::cout << "Test Failed, Wrong exception type!" << std::endl;
    }
    return 0;
}

extern "C" void __libc_init_array();
extern "C" void register_my_posix_tcb();
extern "C" void app_entry() { register_my_posix_tcb(); __libc_init_array(); main(); }

__attribute__((used, section(".bk_app_array")))
static void (*const __bk_app_entry)() = app_entry;
