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

//! Fixed system library catalog.
//!
//! The catalog is the board/product-provided mapping between the names plain
//! `DT_NEEDED` requests search for and the on-device DSO paths. Since the
//! A DSO may omit `DT_SONAME`, so
//! the entry's lookup name and path are independent: `resolve_name` serves
//! plain-name lookups, `resolve_path` decides whether a path-resolved
//! dependency is a shared system DSO (the normalized catalog path is the
//! registry key). Neither operation depends on the ELF carrying `DT_SONAME`.

use blueos_loader::{DependencyName, LoadResult};

/// One fixed mapping from a system lookup name to its on-device path.
#[derive(Clone, Copy, Debug)]
pub struct SystemLibraryEntry {
    /// The plain lookup name, e.g. `b"libc.so.1"`, without a NUL.
    pub lookup_name: &'static [u8],
    /// Absolute device path of the DSO, e.g. `"/system/lib/libc.so.1"`.
    pub path: &'static str,
    /// Quiescence policy: `true` keeps the zero-lease instance cached for later
    /// imports; `false` lets the reaper run its fini and release the backing, so
    /// the next import reloads `generation + 1`. Only make a DSO unloadable
    /// after its address and callback lifetimes are fully modeled.
    pub keep_cached: bool,
}

impl SystemLibraryEntry {
    /// The canonical registry key. System instances are keyed by catalog path,
    /// not by optional ELF `DT_SONAME` metadata.
    pub fn key(&self) -> LoadResult<DependencyName> {
        DependencyName::from_bytes(self.path.as_bytes())
    }
}

/// A fixed, board/product-configured system library catalog.
///
/// The mapping is static: it cannot be mutated at runtime, which keeps the
/// resolver's catalog keyed on immutable byte names rather than a writable
/// directory scan.
pub struct SystemLibraryPaths {
    entries: &'static [SystemLibraryEntry],
}

impl SystemLibraryPaths {
    /// Build a catalog from a static, board-provided entry table.
    pub const fn new(entries: &'static [SystemLibraryEntry]) -> Self {
        Self { entries }
    }

    /// Look up a plain dependency name (a `DT_NEEDED` string without path
    /// separators) by exact, case-sensitive comparison.
    pub fn resolve_name(&self, name: &[u8]) -> Option<&'static SystemLibraryEntry> {
        self.entries.iter().find(|entry| entry.lookup_name == name)
    }

    /// Look up an entry by its normalized absolute device path:
    /// a path-resolved dependency whose path equals a catalog entry's path is
    /// a shared system DSO, whatever `DT_SONAME` it carries. The returned
    /// entry's path doubles as the registry key.
    pub fn resolve_path(&self, path: &str) -> Option<&'static SystemLibraryEntry> {
        self.entries.iter().find(|entry| entry.path == path)
    }

    /// Look up an entry from its canonical registry key.
    pub fn resolve_key(&self, key: &DependencyName) -> Option<&'static SystemLibraryEntry> {
        self.resolve_path(core::str::from_utf8(key.as_bytes()).ok()?)
    }
}
