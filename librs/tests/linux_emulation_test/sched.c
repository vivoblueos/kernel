/*
 * Copyright (c) 2025 vivo Mobile Communication Co., Ltd.
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

#include <unistd.h>
#include <sched.h>

int main()
{
    int priority_max = sched_get_priority_max(SCHED_FIFO);
    if (priority_max == -1)
    {
        write(1, "test failed\n", 12);
        return -1;
    }
    int priority_min = sched_get_priority_min(SCHED_FIFO);
    if (priority_min == -1)
    {
        write(1, "test failed\n", 12);
        return -1;
    }
    if (priority_max < priority_min)
    {
        write(1, "test failed\n", 12);
        return -1;
    }
    write(1, "test passed\n", 12);
    return 0;
}