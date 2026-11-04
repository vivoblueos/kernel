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

use std::{fs::File, io::Write};

pub fn command(args: &[&str]) -> Result<(), String> {
    if let Some(pos) = args.iter().position(|&x| x == ">") {
        if pos + 1 >= args.len() {
            return Err("Missing filename after '>'".to_string());
        }
        let content = &args[..pos];
        let filename = args[pos + 1];
        let mut file =
            File::create(filename).map_err(|e| format!("Failed to create file: {}", e))?;

        writeln!(file, "{}", content.join(" "))
            .map_err(|e| format!("Failed to write to file: {}", e))?;
    } else {
        println!("{}", args.join(" "));
    }

    Ok(())
}
