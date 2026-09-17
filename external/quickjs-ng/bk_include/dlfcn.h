/* Copyright (c) 2026 vivo Mobile Communication Co., Ltd.
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
 * BlueOS newlib compatibility shim for <dlfcn.h>.
 *
 * The toolchain's newlib sysroot has no <dlfcn.h>. quickjs-libc.c's
 * native-module loading uses dlopen/dlsym/dlclose/dlerror and the RTLD_* flag
 * bits. There is no dynamic loading on a statically-linked embedded image, so
 * the implementations in librs/src/syscalls.rs all fail (dlopen returns NULL,
 * dlerror reports the unsupported message). This header is placed earlier on
 * the include path via the engine's bk_include dir.
 */
#ifndef _BLUEOS_COMPAT_DLFCN_H
#define _BLUEOS_COMPAT_DLFCN_H

#ifdef __cplusplus
extern "C" {
#endif

#define RTLD_LAZY   0x00001
#define RTLD_NOW    0x00002
#define RTLD_GLOBAL 0x00100
#define RTLD_LOCAL  0x00000
#define RTLD_DEFAULT ((void *)0)
#define RTLD_NEXT    ((void *)-1)

/* All fail: no dynamic loading on this image (librs/src/syscalls.rs). */
void *dlopen(const char *filename, int flags);
void *dlsym(void *handle, const char *symbol);
int dlclose(void *handle);
char *dlerror(void);

#ifdef __cplusplus
}
#endif

#endif /* _BLUEOS_COMPAT_DLFCN_H */
