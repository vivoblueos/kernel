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

pub fn command(args: &[&str]) -> Result<(), String> {
    if args.len() < 1 {
        return Err("Invalid args".to_string());
    }
    let ptr: usize = if args[0].starts_with("0x") {
        usize::from_str_radix(args[0].strip_prefix("0x").unwrap(), 16)
            .map_err(|_| "Wrong hex format".to_string())?
    } else {
        args[0].parse().map_err(|_| "Wrong format".to_string())?
    };
    unsafe {
        libc::free(ptr as *mut libc::c_void);
    }
    Ok(())
}
