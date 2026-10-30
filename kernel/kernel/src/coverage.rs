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

use minicov::{CoverageWriteError, CoverageWriter};
use semihosting::{c, fs, io, io::Write};

struct SemihostingCoverageWriter<'a> {
    f: &'a mut fs::File,
}

impl<'a> SemihostingCoverageWriter<'a> {
    pub fn new(f: &'a mut fs::File) -> Self {
        Self { f }
    }
}

impl CoverageWriter for SemihostingCoverageWriter<'_> {
    fn write(&mut self, buf: &[u8]) -> Result<(), CoverageWriteError> {
        let Ok(_) = self.f.write(buf) else {
            return Err(CoverageWriteError);
        };
        Ok(())
    }
}

pub fn write_coverage_data() {
    let mut f = fs::File::create(c"output.profraw").unwrap();
    let mut w = SemihostingCoverageWriter::new(&mut f);
    unsafe {
        // Note that this function is not thread-safe! Use a lock if needed.
        minicov::capture_coverage(&mut w).unwrap();
    }
    f.flush();
    semihosting::println!("coverage test end.");
}
