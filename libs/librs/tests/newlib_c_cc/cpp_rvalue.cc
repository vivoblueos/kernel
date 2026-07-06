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
#include <memory>
#include <vector>

struct Widget {
    int id;
    Widget(int i) : id(i) {}
    ~Widget() { }
};

int main() {
    std::vector<std::unique_ptr<Widget>> vec;
    for(int i=0; i<100; ++i) {
        auto p = std::unique_ptr<Widget>(new Widget(i));
        vec.push_back(std::move(p));
    }

    auto shared_w = std::make_shared<Widget>(999);
    auto copy_w = shared_w;
    std::cout << "[Memory Test] Shared Use Count: " << shared_w.use_count() << std::endl;
    if (shared_w.use_count() == 2) {
        std::cout << "[Memory Test] Test passed\n";
    } else {
        std::cout << "[Memory Test] Test failed\n";
    }
    return 0;
}

extern "C" void __libc_init_array();
extern "C" void register_my_posix_tcb();
extern "C" void app_entry() { register_my_posix_tcb(); __libc_init_array(); main(); }

__attribute__((used, section(".bk_app_array")))
static void (*const __bk_app_entry)() = app_entry;
