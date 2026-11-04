// Copyright (c) 2025 vivo Mobile Communication Co., Ltd.
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

extern crate librs;
extern crate rsrt;
use std::{
    io::{self, Write},
    thread,
};

mod commands;
use commands::COMMANDS;

#[cfg(not(enable_vfs))]
compile_error!("Shell app requires vfs to run. Please enable vfs in Kconfig.");

fn main() {
    thread::Builder::new()
        .name("shell".to_string())
        .stack_size(65536)
        .spawn(move || {
            println!("Hello, shell!");
            #[cfg(shell_smoke)]
            {
                run_smoke();
            }
            #[cfg(not(shell_smoke))]
            shell_loop();
        })
        .unwrap()
        .join()
        .unwrap();
}

/// Run one shell command line, reporting whether it succeeded.
///
/// The interactive loop only prints command errors; the smoke sequence needs a
/// verdict per command so a failing step cannot be hidden by a later success.
fn execute_checked(input: &str) -> bool {
    let parts: Vec<&str> = input.split_whitespace().collect();
    if parts.is_empty() {
        return false;
    }
    let cmd = parts[0];
    let args = &parts[1..];
    match COMMANDS.get(cmd) {
        Some(info) => match (info.handler)(args) {
            Ok(()) => true,
            Err(e) => {
                println!("Error: {}", e);
                false
            }
        },
        None => {
            println!("Unknown command: {}", cmd);
            false
        }
    }
}

fn shell_loop() {
    loop {
        print!("> ");
        io::stdout().flush().unwrap();
        let mut input = String::new();
        if io::stdin().read_line(&mut input).unwrap() == 0 {
            break;
        }
        let input = input.trim();
        if input == "exit" {
            break;
        }

        if input.is_empty() {
            continue;
        }

        execute_checked(input);
    }
}

/// Non-interactive smoke sequence used by the QEMU boot check.
///
/// QEMU runners redirect the serial port to a file, so nothing can type into
/// the prompt. This mode drives the same command table from a fixed script and
/// prints one terminal line the checker can assert on.
#[cfg(shell_smoke)]
fn run_smoke() {
    // The scratch tree lives where the board can actually write. Boards with
    // `--cfg fatfs` mount the block image at /fat and exercise that driver;
    // boards without block storage (qemu_riscv64 only builds the root
    // filesystem) must not be sent down the /fat path or mkdir fails with
    // EINVAL and the smoke never reaches its terminal PASS line.
    #[cfg(fatfs)]
    const COMMANDS: &[&str] = &[
        "pwd",
        "mkdir /fat/shell-smoke",
        "echo hello-smoke > /fat/shell-smoke/a.txt",
        "cat /fat/shell-smoke/a.txt",
        "ls /fat/shell-smoke",
        "cmp /fat/shell-smoke/a.txt /fat/shell-smoke/a.txt",
        "ps",
    ];
    #[cfg(not(fatfs))]
    const COMMANDS: &[&str] = &[
        "pwd",
        "mkdir /shell-smoke",
        "echo hello-smoke > /shell-smoke/a.txt",
        "cat /shell-smoke/a.txt",
        "ls /shell-smoke",
        "cmp /shell-smoke/a.txt /shell-smoke/a.txt",
        "ps",
    ];
    for cmd in COMMANDS {
        println!("$ {}", cmd);
        if !execute_checked(cmd) {
            println!("SHELL-SMOKE-FAIL {}", cmd);
            return;
        }
    }
    println!("SHELL-SMOKE-PASS");
}
