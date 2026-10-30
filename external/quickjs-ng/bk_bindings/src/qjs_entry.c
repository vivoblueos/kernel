// Copyright (c) 2026 vivo Mobile Communication Co., Ltd.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//       http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

// BlueOS QuickJS front-end (C entry).
//
// This is a plain C application linked by the toolchain's GCC against
// newlib (libc.a) plus the librs newlib-adapter static archive — there is no
// Rust `std`/`rsrt` in the loop (the same model as librs/tests/newlib_c_cc).
// The kernel picks the entry up from the `.bk_app_array` section after boot.
//
// Two modes, selected at compile time by the `QUICKJS_CHECK` macro:
//   - REPL (default): hand control to the engine's own `qjs` shell `main()`,
//     which with no file/expr argument drops into the interactive
//     read-eval-print loop (js_std_eval_binary(qjsc_repl) + js_std_loop).
//   - qjs_check     : evaluate a fixed set of JS snippets through the engine
//     C API and print QUICKJS_CHECK_PASS / QUICKJS_CHECK_FAIL so the QEMU
//     checker can assert success and terminate the emulator.

#include <pthread.h>
#include <stdio.h>
#include <string.h>

#include "quickjs-libc.h"
#include "quickjs.h"

// Kernel/newlib runtime entry contracts (provided by the librs adapter).
extern void register_my_posix_tcb(void);
extern void __libc_init_array(void);

#ifndef QUICKJS_CHECK

// ---- interactive REPL -----------------------------------------------------
// Reuse the engine shell's own main(). With no -e/-i it sets interactive mode
// and runs the compiled-in repl.js REPL.
//
// We pass `--stack-size` explicitly. The engine otherwise assumes a
// JS_DEFAULT_STACK_SIZE (1 MiB) budget: on a much smaller real thread stack
// its own overflow guard (stack_top - stack_size) sits *below* the live SP, so
// it never trips and recursion runs past the guard band, corrupting memory
// (observed as a Bus Fault in find_own_property on any REPL input). Capping the
// assumed stack to the real budget makes QuickJS raise a catchable
// "InternalError: stack overflow" before the hardware stack is exhausted.
extern int main(int argc, char **argv);

// Value handed to qjs's `--stack-size`, which forwards it to
// JS_SetMaxStackSize as the JS-engine stack budget. The shell runs on the
// dedicated large-stack pthread below, so this just needs to stay comfortably
// under that pthread's stack so the C frames of the interpreter itself still
// fit below the JS guard.
//
// qjs's --stack-size goes through parse_limit(), whose *bare* numbers are in
// kibibytes (unit=1024), not bytes; it accepts only a plain integer token
// (optionally with a k/m/g suffix). So this macro must expand to a single
// integer token, e.g. "32" -> parse_limit -> 32*1024 = 32768 bytes.
#ifndef QUICKJS_REPL_STACK_SIZE_KB
#define QUICKJS_REPL_STACK_SIZE_KB 32
#endif

#define QUICKJS_STR_(x) #x
#define QUICKJS_STR(x) QUICKJS_STR_(x)

// The REPL drives deep call chains (QuickJS interpreter -> newlib fopen ->
// BlueOS VFS open) when std.loadFile runs, which overflows the app thread's
// default 12 KiB stack and corrupts adjacent heap. Run the shell on a
// dedicated pthread with a much larger stack instead. The size is provided by
// the librs pthread implementation (syncs.rs), whose pthread_create reads the
// stack size back out of the attr it initialized; it must stay a multiple of
// STACK_ALIGN (8 bytes on this target).
#ifndef QUICKJS_REPL_PTHREAD_STACK_SIZE
#define QUICKJS_REPL_PTHREAD_STACK_SIZE (64 * 1024)
#endif

static void *quickjs_repl_thread(void *unused) {
    (void)unused;
    static char *argv[] = {
        (char *)"qjs",
        (char *)"--stack-size",
        (char *)QUICKJS_STR(QUICKJS_REPL_STACK_SIZE_KB),
    };
    main(3, argv);
    return NULL;
}

static void quickjs_app_main(void) {
    pthread_attr_t attr;
    pthread_t tid;

    if (pthread_attr_init(&attr) != 0) {
        printf("quickjs: pthread_attr_init failed\n");
        return;
    }
    pthread_attr_setstacksize(&attr, QUICKJS_REPL_PTHREAD_STACK_SIZE);
    if (pthread_create(&tid, &attr, quickjs_repl_thread, NULL) != 0) {
        printf("quickjs: pthread_create failed\n");
        return;
    }
    pthread_attr_destroy(&attr);
    pthread_join(tid, NULL);
}

#else

// ---- scripted qjs_check run ------------------------------------------------
// (source, expected printed value); expected == NULL means an exception.
struct check_case {
    const char *src;
    const char *expected; /* NULL => expect an exception */
};

static const struct check_case kCases[] = {
    { "1+2", "3" },
    { "\"a\"+\"b\"", "ab" },
    { "(function fib(n){return n<2?n:fib(n-1)+fib(n-2)})(10)", "55" },
    { "syntax error here", NULL },
    { "throw new Error('boom')", NULL },
};

static void eval_case(JSContext *ctx, const struct check_case *c, int *pass) {
    JSValue v = JS_Eval(ctx, c->src, strlen(c->src), "<qjs_check>", JS_EVAL_TYPE_GLOBAL);
    int is_exc = JS_IsException(v);
    char buf[256];
    const char *rendered = buf;

    if (is_exc) {
        JSValue exc = JS_GetException(ctx);
        const char *s = JS_ToCString(ctx, exc);
        snprintf(buf, sizeof(buf), "Error: %s", s ? s : "exception");
        if (s) JS_FreeCString(ctx, s);
        JS_FreeValue(ctx, exc);
    } else {
        const char *s = JS_ToCString(ctx, v);
        snprintf(buf, sizeof(buf), "%s", s ? s : "");
        if (s) JS_FreeCString(ctx, s);
    }

    int ok = c->expected ? (!is_exc && strcmp(buf, c->expected) == 0) : is_exc;
    printf("CHECK %s | %s => %s\n", ok ? "ok" : "FAIL", c->src, rendered);
    if (!ok) *pass = 0;
    JS_FreeValue(ctx, v);
}

static void quickjs_app_main(void) {
    JSRuntime *rt = JS_NewRuntime();
    if (!rt) {
        printf("quickjs: failed to create runtime\n");
        printf("QUICKJS_CHECK_FAIL\n");
        return;
    }
    js_std_init_handlers(rt);
    JSContext *ctx = JS_NewContext(rt);
    if (!ctx) {
        printf("quickjs: failed to create context\n");
        printf("QUICKJS_CHECK_FAIL\n");
        js_std_free_handlers(rt);
        JS_FreeRuntime(rt);
        return;
    }

    int pass = 1;
    size_t i;
    for (i = 0; i < sizeof(kCases) / sizeof(kCases[0]); i++) {
        eval_case(ctx, &kCases[i], &pass);
    }

    printf(pass ? "QUICKJS_CHECK_PASS\n" : "QUICKJS_CHECK_FAIL\n");

    JS_FreeContext(ctx);
    js_std_free_handlers(rt);
    JS_FreeRuntime(rt);
}

#endif /* QUICKJS_CHECK */

// BlueOS app entry. Runs on a kernel thread with a stack sized by app.conf.
void app_entry(void) {
    register_my_posix_tcb();
    __libc_init_array();
    quickjs_app_main();
}

__attribute__((used, section(".bk_app_array")))
static void (*const __bk_app_entry)(void) = app_entry;
