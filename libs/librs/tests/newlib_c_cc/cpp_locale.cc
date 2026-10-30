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
#include <stdlib.h>
#include <locale.h>
#include <wchar.h>

#pragma GCC optimize ("O0")
int main() {
    setlocale(LC_CTYPE, "UTF-8");
    const char* u8_str = "嵌入式系统";
    wchar_t w_buf[32] = {0};
    size_t result = mbstowcs(w_buf, u8_str, sizeof(w_buf)/sizeof(wchar_t));

    if (result == (size_t)-1) {
        printf("转换失败：遭遇非法编码！\n");
    } else {
        for(size_t i = 0; i < result; i++) {
            printf("汉字[%zu] 码点: U+%04X\n", i, (unsigned int)w_buf[i]);
        }
        printf("test passed\n");
    }

}

extern "C" void __libc_init_array();
extern "C" void register_my_posix_tcb();
extern "C" void app_entry() { register_my_posix_tcb(); __libc_init_array(); main(); }

__attribute__((used, section(".bk_app_array")))
static void (*const __bk_app_entry)() = app_entry;