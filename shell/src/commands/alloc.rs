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
    if args.len() < 2 {
        return Err("Invalid args".to_string());
    }
    let size: usize = args[0].parse().map_err(|_| "Wrong format".to_string())?;
    let align: usize = args[1].parse().map_err(|_| "Wrong format".to_string())?;
    let mut result: *mut libc::c_void = std::ptr::null_mut();
    unsafe {
        let rc = libc::posix_memalign(
            &mut result as *mut _,
            align as libc::size_t,
            size as libc::size_t,
        );
        if rc != 0 || result.is_null() {
            return Err("Unable to allocate memory".to_string());
        }
    }
    println!("{:?}", result);
    Ok(())
}
