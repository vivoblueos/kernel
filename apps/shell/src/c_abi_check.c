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

/*
 * The C ABI the shell is built against.
 *
 * `apps/shell` itself is Rust, but it links librs and it starts C programs,
 * so the C view of a synchronization object has to be the kernel's view:
 * `pthread_mutex_t` is 24 bytes of mutex in librs, while newlib's
 * <sys/_pthreadtypes.h> describes it as a 4-byte index into a process-wide
 * table. A translation unit that picks up newlib's typedef allocates four
 * bytes on the stack and librs then writes 24 into them.
 *
 * Nothing here is executed and no symbol is referenced - the assertions fire
 * at compile time. What this file really tests is the *build*: it compiles
 * with the flags of the shell target, so the header path has to arrive
 * through `//librs`'s public config. When it does not, newlib's header is
 * used, `sizeof` is 4, and the build stops here instead of corrupting memory
 * at run time.
 *
 * The same values are asserted from the C side in librs/tests/posix
 * (`issue8_clock.c`) and from the Rust side in librs/src/sync/abi.rs; this
 * one is the third corner, the application.
 */

#include <pthread.h>
#include <stddef.h>

_Static_assert(sizeof(pthread_mutex_t) == 24,
               "pthread_mutex_t must be librs' 24-byte object; is //librs/include on the include path?");

_Static_assert(_Alignof(pthread_mutex_t) == 8,
               "pthread_mutex_t must be 8-byte aligned, as the kernel's object is");

_Static_assert(sizeof(pthread_cond_t) == 24,
               "pthread_cond_t must be librs' 24-byte object, not newlib's 4-byte index");
