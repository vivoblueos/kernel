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

fn main() {
    thread::Builder::new()
        .name("shell".to_string())
        .stack_size(65536)
        .spawn(move || {
            println!("Hello, shell!");
            shell_loop();
        })
        .unwrap()
        .join()
        .unwrap();
}

fn shell_loop() {
    loop {
        print!("> ");
        io::stdout().flush().unwrap();
        let mut input = String::new();
        io::stdin().read_line(&mut input).unwrap();
        let input = input.trim();
        if input == "exit" {
            break;
        }

        if input.is_empty() {
            continue;
        }

        let parts: Vec<&str> = input.split_whitespace().collect();
        let cmd = parts[0];
        let args = &parts[1..];
        match COMMANDS.get(cmd) {
            Some(info) => {
                if let Err(e) = (info.handler)(args) {
                    println!("Error: {}", e);
                }
            }
            None => println!("Unknown command: {}", cmd),
        }
    }
}
