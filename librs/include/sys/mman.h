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
 * <sys/mman.h> for BlueOS.
 *
 * newlib 4.4.0 does not ship this header at all, so a C program that calls
 * mmap() cannot even name PROT_READ today. librs implements mmap()/munmap()
 * (anonymous mappings only - the kernel refuses a file-backed request with
 * EINVAL rather than returning zero-filled memory), so the declarations come
 * from here.
 *
 * Only the memory-mapping subset is declared. POSIX also puts msync(),
 * mlock()/munlock(), posix_madvise() and the typed memory objects here; none
 * of them exist on this kernel yet, and declaring a function nobody implements
 * would turn a compile error into a link error - the wrong place to find out.
 *
 * The constants must agree with the kernel's `user::sys_mmap`, which checks
 * them by value: PROT_READ/WRITE/EXEC are the low three bits (a request with
 * none of them is refused), and exactly one of MAP_SHARED / MAP_PRIVATE is
 * required.
 */

#ifndef LIBRS_INCLUDE_SYS_MMAN_H
#define LIBRS_INCLUDE_SYS_MMAN_H

#include <stddef.h>
#include <sys/types.h>

#ifdef __cplusplus
extern "C" {
#endif

#define PROT_NONE 0x0
#define PROT_READ 0x1
#define PROT_WRITE 0x2
#define PROT_EXEC 0x4

#define MAP_SHARED 0x01
#define MAP_PRIVATE 0x02
#define MAP_FIXED 0x10
#define MAP_ANONYMOUS 0x20
#define MAP_ANON MAP_ANONYMOUS

#define MAP_FAILED ((void *)-1)

void *mmap(void *addr, size_t len, int prot, int flags, int fildes, off_t off);
int munmap(void *addr, size_t len);

#ifdef __cplusplus
}
#endif

#endif /* LIBRS_INCLUDE_SYS_MMAN_H */
