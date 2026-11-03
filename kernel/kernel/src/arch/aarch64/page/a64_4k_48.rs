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

use tock_registers::register_bitfields;

pub type PageEntry = super::a64_4k::PageEntry<4>;

register_bitfields! {usize,
    pub PAGE_FORMAT [
        /// VA[47:39].
        INDEX0 OFFSET(39) NUMBITS(9) [],
        /// VA[38:30].
        INDEX1 OFFSET(30) NUMBITS(9) [],
        /// VA[29:21].
        INDEX2 OFFSET(21) NUMBITS(9) [],
        /// VA[20:12].
        INDEX3 OFFSET(12) NUMBITS(9) [],
        PAGE_OFFSET OFFSET(0) NUMBITS(12) [],
    ]
}
