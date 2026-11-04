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

#include <stdio.h>
#include <time.h>

int main(void)
{
    struct timespec current_time, sleep_time, after_sleep_time;
    if (clock_gettime(CLOCK_REALTIME, &current_time) != 0) {
        write(1, "Failed to get current time\n", 27);
        return -1;
    }
    sleep_time.tv_sec = 0;
    sleep_time.tv_nsec = 5000000; // 5 milliseconds
    if (clock_nanosleep(CLOCK_REALTIME, 0, &sleep_time, NULL) != 0) {
        write(1, "Failed to sleep\n", 16);
        return -1;
    }
    if (clock_gettime(CLOCK_REALTIME, &after_sleep_time) != 0) {
        write(1, "Failed to get time after sleep\n", 30);
        return -1;
    }
    // Check if the time after sleep is greater than the time before sleep
    if (after_sleep_time.tv_sec > current_time.tv_sec ||
        (after_sleep_time.tv_sec == current_time.tv_sec && 
         after_sleep_time.tv_nsec - current_time.tv_nsec > 5000000)) {
        write(1, "Test PASSED\n", 12);
        return 0;
    } else {
        write(1, "Test FAILED\n", 12);
        return -1;
    }
}
