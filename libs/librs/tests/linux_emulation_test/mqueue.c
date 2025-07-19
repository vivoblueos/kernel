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

#include <mqueue.h>
#include <unistd.h>
#include <sys/stat.h>
#include <fcntl.h>

static const char *msg = "Hello, World!";
static const char *name = "/test_mq";
int main()
{
    mqd_t mq;

    mq = mq_open(name, O_CREAT | O_RDWR, S_IWUSR | S_IRUSR, NULL);
    if (mq == (mqd_t) -1)
    {
        write(1, "test failed\n", 12);
        return -1;
    }
    if (mq_send(mq, msg, 13, 1) != 0)
    {
        write(1, "test failed\n", 12);
        mq_close(mq);
        return -1;
    }
    mq_close(mq);
    mq_unlink(name);
    write(1, "test passed\n", 12);
    return 0;
}