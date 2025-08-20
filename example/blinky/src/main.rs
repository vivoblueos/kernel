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

use std::io::Write;

fn main() -> std::io::Result<()> {
    println!("Running BlueOS Pico2 Blinky Example!");

    let mut file = std::fs::OpenOptions::new().write(true).open("/dev/led0")?;
    let mut is_light_on = false;

    loop {
        if is_light_on {
            file.write_all(b"0")?;
        } else {
            file.write_all(b"1")?;
        }
        is_light_on = !is_light_on; // Toggle the LED state
        let _d = librs::time::msleep(1000);
    }

    Ok(())
}
