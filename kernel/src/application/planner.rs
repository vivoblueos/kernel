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

//! BFS launch planner over the read-only dependency scan.
//!
//! The planner walks the real `DT_NEEDED` graph from the launch root: open
//! each file, scan it with the loader's [`scan_artifact`], classify every
//! dependency request through the namespace rules, and record the images and
//! edges of the whole closure. The output [`NamespaceLoadPlan`] is a transient
//! object describing this launch as observed from the VFS.
//!
//! Its purpose: the launch path sees the complete system closure
//! before linking, so the system permits can be acquired as one atomic batch
//! instead of one-by-one (which would risk an ABBA deadlock between two
//! concurrent sessions).

use alloc::{
    string::{String, ToString},
    vec::Vec,
};

use blueos_loader::{
    scan_artifact, ArtifactIdentity, ArtifactRole, DependencyName, LoadError, LoadErrorKind,
    LoadResult, ScannedArtifact, SessionLimits,
};

use crate::{
    application::{
        adapters::{
            resolver::identity_from_path,
            system_paths::{SystemLibraryEntry, SystemLibraryPaths},
            vfs_reader::VfsElfReader,
        },
        namespace::{resolve_dependency_paths, ApplicationNamespace, DependencyKind, ResolveBase},
    },
    error::code,
    vfs::open_path,
};

/// One planned image: its resolved path, identity and scanned metadata.
pub struct PlannedImage {
    /// The normalized absolute path this image was opened at.
    path: String,
    /// The path-derived graph deduplication key.
    identity: ArtifactIdentity,
    /// Canonical path key when this is a shared system DSO. `None` means the
    /// image belongs only to this application namespace.
    system_key: Option<DependencyName>,
    /// What the scan saw: the optional SONAME and the `DT_NEEDED` set, in
    /// encounter order.
    scanned: ScannedArtifact,
}

impl PlannedImage {
    /// The normalized absolute path this image was planned at.
    pub fn path(&self) -> &str {
        &self.path
    }

    /// The artifact identity used by the linker graph.
    pub fn identity(&self) -> &ArtifactIdentity {
        &self.identity
    }

    /// Whether the planner classified this image as a shared system DSO.
    pub fn system(&self) -> bool {
        self.system_key.is_some()
    }

    /// The canonical registry key for a system image.
    pub fn system_key(&self) -> Option<&DependencyName> {
        self.system_key.as_ref()
    }

    /// The scanned metadata (SONAME + needed, in order).
    pub fn scanned(&self) -> &ScannedArtifact {
        &self.scanned
    }
}

/// One dependency edge: requester → provider.
pub struct PlannedEdge {
    /// The index of the requesting image in the plan.
    requester: usize,
    /// The raw `DT_NEEDED` string as scanned (before classification).
    request: DependencyName,
    /// The index of the image the request resolved to.
    provider: usize,
}

impl PlannedEdge {
    /// The requesting image's index.
    pub fn requester(&self) -> usize {
        self.requester
    }

    /// The raw request string.
    pub fn request(&self) -> &DependencyName {
        &self.request
    }

    /// The provider image's index.
    pub fn provider(&self) -> usize {
        self.provider
    }
}

/// The transient launch plan: every image in the closure, every edge, and the
/// deduplicated system catalog keys the launch will batch-acquire.
pub struct NamespaceLoadPlan {
    images: Vec<PlannedImage>,
    edges: Vec<PlannedEdge>,
    /// The sorted, deduplicated system catalog paths the closure touches.
    system_keys: Vec<DependencyName>,
}

impl NamespaceLoadPlan {
    /// Every planned image, in BFS discovery order.
    pub fn images(&self) -> &[PlannedImage] {
        &self.images
    }

    /// Every dependency edge, in BFS order.
    pub fn edges(&self) -> &[PlannedEdge] {
        &self.edges
    }

    /// The system catalog keys (sorted, deduplicated) this launch needs:
    /// the batch-acquire input.
    pub fn system_keys(&self) -> &[DependencyName] {
        &self.system_keys
    }
}

/// The BFS planner: scan the real dependency closure of one launch.
pub struct NamespaceLoadPlanner<'a> {
    namespace: &'a ApplicationNamespace,
    system_catalog: &'static SystemLibraryPaths,
    limits: SessionLimits,
}

impl<'a> NamespaceLoadPlanner<'a> {
    /// Plan over `namespace`'s frozen launch state, the system catalog and
    /// the session limits.
    pub fn new(
        namespace: &'a ApplicationNamespace,
        system_catalog: &'static SystemLibraryPaths,
        limits: SessionLimits,
    ) -> Self {
        Self {
            namespace,
            system_catalog,
            limits,
        }
    }

    /// Walk the closure from the namespace's root path.
    ///
    /// Each discovered image is scanned read-only and assigned an identity
    /// derived from its normalized path.
    pub fn plan(&self) -> LoadResult<NamespaceLoadPlan> {
        let root_path = self.namespace.root_path();
        let mut images: Vec<PlannedImage> = Vec::new();
        let mut edges: Vec<PlannedEdge> = Vec::new();
        let mut system_keys: Vec<DependencyName> = Vec::new();

        // Seed the root: an exact open, no fallback. The BFS queue
        // pairs each image with its depth so the session's
        // dependency-depth limit bounds the longest chain, not the image
        // count.
        let mut queue: Vec<(usize, u16)> = Vec::new();
        let mut queue_head = 0;
        let root = self.open_and_scan(root_path, ArtifactRole::ExecutableRoot)?;
        images.push(root);
        queue.push((0, 1));

        while queue_head < queue.len() {
            let (requester_index, depth) = queue[queue_head];
            queue_head += 1;
            // The requester's own directory: relative DT_NEEDED resolve
            // against the requesting ELF's directory.
            let requester_dir = parent_dir(&images[requester_index].path);
            let requester_is_system = images[requester_index].system();
            let needed: Vec<DependencyName> = images[requester_index].scanned().needed.to_vec();
            for request in needed {
                self.limits
                    .check_dependency_edge_count((edges.len() + 1) as u32)?;
                let (provider_index, is_new) = self.resolve_request(
                    &mut images,
                    &mut system_keys,
                    &requester_dir,
                    requester_is_system,
                    &request,
                )?;
                edges.push(PlannedEdge {
                    requester: requester_index,
                    request,
                    provider: provider_index,
                });
                if is_new {
                    let next_depth = depth + 1;
                    self.limits.check_dependency_depth(next_depth)?;
                    queue.push((provider_index, next_depth));
                }
            }
        }

        system_keys.sort();
        system_keys.dedup();
        self.limits.check_image_count(images.len() as u32)?;
        Ok(NamespaceLoadPlan {
            images,
            edges,
            system_keys,
        })
    }

    /// Resolve one dependency request to a planned image index, opening and
    /// scanning the file on first sight.
    ///
    /// Returns the provider's index in `images` and whether the image was
    /// discovered by this request (`true`) or already planned (`false`); on
    /// success a newly discovered image has been appended to `images` and,
    /// when it is a system DSO, its catalog path added to `system_keys`.
    fn resolve_request(
        &self,
        images: &mut Vec<PlannedImage>,
        system_keys: &mut Vec<DependencyName>,
        requester_dir: &str,
        requester_is_system: bool,
        request: &DependencyName,
    ) -> LoadResult<(usize, bool)> {
        let request_str = core::str::from_utf8(request.as_bytes()).map_err(|_| {
            LoadError::new(
                LoadErrorKind::BadElf,
                blueos_loader::ErrorContext::Dependency {
                    requester: 0,
                    needed: request.as_bytes().into(),
                },
            )
        })?;
        let kind = DependencyKind::classify(request_str);

        // A system DSO requester never resolves against the application
        // namespace: its relocations must be identical no matter
        // which application first triggered its load.
        let candidates: Vec<String> = if requester_is_system {
            match kind {
                DependencyKind::Absolute | DependencyKind::Relative => {
                    // Path requests from a system DSO must hit the catalog.
                    let mut resolved = resolve_dependency_paths(
                        self.namespace,
                        ResolveBase::RequesterDirectory(requester_dir),
                        request_str,
                    );
                    resolved.retain(|path| self.system_catalog.resolve_path(path).is_some());
                    resolved
                }
                DependencyKind::PlainName => {
                    match self.system_catalog.resolve_name(request.as_bytes()) {
                        Some(entry) => Vec::from([entry.path.to_string()]),
                        None => Vec::new(),
                    }
                }
            }
        } else {
            match kind {
                DependencyKind::Absolute | DependencyKind::Relative => resolve_dependency_paths(
                    self.namespace,
                    ResolveBase::RequesterDirectory(requester_dir),
                    request_str,
                ),
                DependencyKind::PlainName => {
                    // Private lib first; fall through to the catalog on
                    // ENOENT only.
                    let private = resolve_dependency_paths(
                        self.namespace,
                        ResolveBase::RequesterDirectory(requester_dir),
                        request_str,
                    );
                    if !self.first_is_missing(&private) {
                        private
                    } else {
                        match self.system_catalog.resolve_name(request.as_bytes()) {
                            Some(entry) => Vec::from([entry.path.to_string()]),
                            // Keep the private candidate so the open reports
                            // the actual ENOENT path.
                            None => private,
                        }
                    }
                }
            }
        };

        if candidates.is_empty() {
            return Err(unresolved(request));
        }

        // Try candidates in order: a missing file advances to the next; a
        // present-but-unloadable file fails without fallback.
        let mut last_error = unresolved(request);
        for candidate in candidates {
            // Path dedup: the same resolved path is the same image.
            if let Some(index) = images.iter().position(|image| image.path == candidate) {
                return Ok((index, false));
            }
            match self.open_and_scan(&candidate, ArtifactRole::SharedObject) {
                Ok(image) => {
                    if let Some(index) = images.iter().position(|existing| {
                        existing.identity == image.identity && existing.system() == image.system()
                    }) {
                        return Ok((index, false));
                    }
                    let system_key = image.system_key.clone();
                    images.push(image);
                    if let Some(key) = system_key {
                        system_keys.push(key);
                    }
                    return Ok((images.len() - 1, true));
                }
                Err(error) => {
                    if self.is_enoent(&candidate) {
                        last_error = error;
                        continue;
                    }
                    return Err(error);
                }
            }
        }
        Err(last_error)
    }

    /// Open `path` and scan it read-only. `role` is `ExecutableRoot` for the launch root and
    /// `SharedObject` for every dependency.
    fn open_and_scan(&self, path: &str, role: ArtifactRole) -> LoadResult<PlannedImage> {
        let file = open_path(path, libc::O_RDONLY, 0).map_err(|_| backend_error())?;
        let reader = VfsElfReader::new(file);
        let scanned = scan_artifact(
            &reader,
            self.namespace.profile(),
            role,
            *self.limits.per_image(),
        )?;
        // A path that equals a catalog entry's path is a shared system DSO
        // whatever DT_SONAME it carries.
        let entry = if role == ArtifactRole::SharedObject {
            self.system_catalog.resolve_path(path)
        } else {
            None
        };
        let identity = identity_from_path(path);
        Ok(PlannedImage {
            path: path.to_string(),
            identity,
            system_key: entry.map(SystemLibraryEntry::key).transpose()?,
            scanned,
        })
    }

    /// Whether the first private candidate is absent. Only `ENOENT` and
    /// `ENOTDIR` permit a system fallback; every other open error keeps the
    /// private candidate selected so the launch fails on that exact path.
    fn first_is_missing(&self, paths: &[String]) -> bool {
        match paths.first() {
            Some(path) => matches!(
                open_path(path, libc::O_RDONLY, 0),
                Err(error) if error == code::ENOENT || error == code::ENOTDIR
            ),
            None => true,
        }
    }

    /// Whether an open of `path` fails with the "not present" errno family
    /// (: only `ENOENT`/`ENOTDIR` advance the search).
    fn is_enoent(&self, path: &str) -> bool {
        matches!(
            open_path(path, libc::O_RDONLY, 0),
            Err(error) if error == code::ENOENT || error == code::ENOTDIR
        )
    }
}

fn unresolved(request: &DependencyName) -> LoadError {
    LoadError::new(
        LoadErrorKind::Backend,
        blueos_loader::ErrorContext::Dependency {
            requester: 0,
            needed: request.as_bytes().into(),
        },
    )
}

fn backend_error() -> LoadError {
    LoadError::new(LoadErrorKind::Backend, blueos_loader::ErrorContext::None)
}

/// The parent directory of an absolute normalized path: everything before
/// the final `/` component, or `/` for top-level entries.
fn parent_dir(path: &str) -> String {
    let trimmed = path.trim_end_matches('/');
    match trimmed.rfind('/') {
        Some(0) => "/".to_string(),
        Some(at) => trimmed[..at].to_string(),
        None => "/".to_string(),
    }
}

#[cfg(test)]
mod tests {
    use alloc::{vec, vec::Vec};
    use blueos_loader::SessionLimits;
    use blueos_test_macro::test;
    #[cfg(use_defmt)]
    use defmt::println;
    #[cfg(not(use_defmt))]
    use semihosting::println;

    use super::*;
    use crate::application::{
        adapters::system_paths::SystemLibraryEntry, namespace::ApplicationNamespace,
    };

    /// The test catalog mirrors the boot runtime's: two system DSOs
    /// keyed by name and path.
    static TEST_CATALOG: SystemLibraryPaths = SystemLibraryPaths::new(&[
        SystemLibraryEntry {
            lookup_name: b"libc.so.1",
            path: "/system/lib/libc.so.1",
            keep_cached: true,
        },
        SystemLibraryEntry {
            lookup_name: b"libsys_extra.so.1",
            path: "/system/lib/libsys_extra.so.1",
            keep_cached: false,
        },
    ]);

    /// A minimal but structurally valid ELF32 DSO fixture the planner can
    /// scan: one PT_LOAD, a PT_DYNAMIC whose `DT_NEEDED`s reference a
    /// dynstr placed inside the PT_LOAD's file range. vaddr == file offset
    /// for the whole file keeps the strtab/needed offsets trivial.
    ///
    /// Layout: ehdr(52) | phdrs(2*32) | dynamic | dynstr, all mapped by one
    /// PT_LOAD at vaddr 0x1000 (p_offset 0, so vaddr = 0x1000 + file).
    fn dso_elf(needed: &[&str], soname: Option<&str>) -> Vec<u8> {
        // dynstr: NUL-joined names, prefixed by a 1-byte padding NUL so
        // every name offset is >= 1 (offset 0 would be an empty name).
        let mut dynstr: Vec<u8> = vec![0];
        let mut offsets = Vec::new();
        for name in needed.iter().chain(soname.iter()) {
            offsets.push(dynstr.len());
            dynstr.extend_from_slice(name.as_bytes());
            dynstr.push(0);
        }
        // The dynstr's vaddr: the PT_LOAD maps file offset `str_off` at
        // vaddr 0x1000 + str_off. Two name-position entries always come
        // first, so dyn_len (and thus str_off) is computable up front.
        let dyn_len = (2 + needed.len() + usize::from(soname.is_some()) + 1) * 8;
        let str_off = DYN_OFF + dyn_len;
        let strsz = dynstr.len();
        let mut entries: Vec<(u32, u64)> = vec![
            (DT_STRTAB, 0x1000 + str_off as u64),
            (DT_STRSZ, strsz as u64),
        ];
        for &offset in &offsets[..needed.len()] {
            entries.push((DT_NEEDED, offset as u64));
        }
        if soname.is_some() {
            entries.push((DT_SONAME, offsets[needed.len()] as u64));
        }

        let mut bytes = vec![0u8; str_off + strsz];
        // ehdr
        bytes[..4].copy_from_slice(b"\x7fELF");
        bytes[4] = 1; // ELFCLASS32
        bytes[5] = 1; // ELFDATA2LSB
        bytes[6] = 1; // EV_CURRENT
        bytes[16..18].copy_from_slice(&(ET_DYN as u16).to_le_bytes()); // e_type
        bytes[18..20].copy_from_slice(&(EM_ARM as u16).to_le_bytes()); // e_machine
        bytes[20..24].copy_from_slice(&1u32.to_le_bytes()); // e_version
        bytes[28..32].copy_from_slice(&(ELF32_EHDR_SIZE as u32).to_le_bytes()); // e_phoff

        // e_flags: EABI5 | EF_ARM_ABI_FLOAT_SOFT, as required by the
        // arm_thumb_soft_float profile.
        bytes[36..40].copy_from_slice(&0x0500_0200u32.to_le_bytes());
        bytes[40..42].copy_from_slice(&(ELF32_EHDR_SIZE as u16).to_le_bytes()); // e_ehsize
        bytes[42..44].copy_from_slice(&(32u16).to_le_bytes()); // e_phentsize
        bytes[44..46].copy_from_slice(&2u16.to_le_bytes()); // e_phnum

        // PT_LOAD: r-x, covering the whole file at vaddr 0x1000. ELF32 phdr
        // field order: type, offset, vaddr, paddr, filesz, memsz, flags, align.
        let ph0 = ELF32_EHDR_SIZE;
        let file_len = bytes.len() as u32;
        bytes[ph0..ph0 + 4].copy_from_slice(&1u32.to_le_bytes()); // p_type = PT_LOAD
        bytes[ph0 + 4..ph0 + 8].copy_from_slice(&0u32.to_le_bytes()); // p_offset
        bytes[ph0 + 8..ph0 + 12].copy_from_slice(&0x1000u32.to_le_bytes()); // p_vaddr
        bytes[ph0 + 12..ph0 + 16].copy_from_slice(&0x1000u32.to_le_bytes()); // p_paddr
        bytes[ph0 + 16..ph0 + 20].copy_from_slice(&file_len.to_le_bytes()); // p_filesz
        bytes[ph0 + 20..ph0 + 24].copy_from_slice(&file_len.to_le_bytes()); // p_memsz
        bytes[ph0 + 24..ph0 + 28].copy_from_slice(&5u32.to_le_bytes()); // p_flags = R|X
        bytes[ph0 + 28..ph0 + 32].copy_from_slice(&4u32.to_le_bytes()); // p_align

        // PT_DYNAMIC uses the same ELF32 field order.
        let ph1 = ph0 + 32;
        bytes[ph1..ph1 + 4].copy_from_slice(&2u32.to_le_bytes()); // p_type = PT_DYNAMIC
        bytes[ph1 + 4..ph1 + 8].copy_from_slice(&(DYN_OFF as u32).to_le_bytes()); // p_offset
        bytes[ph1 + 8..ph1 + 12].copy_from_slice(&(0x1000 + DYN_OFF as u32).to_le_bytes()); // p_vaddr
        bytes[ph1 + 12..ph1 + 16].copy_from_slice(&(DYN_OFF as u32).to_le_bytes()); // p_paddr
        bytes[ph1 + 16..ph1 + 20].copy_from_slice(&(dyn_len as u32).to_le_bytes()); // p_filesz
        bytes[ph1 + 20..ph1 + 24].copy_from_slice(&(dyn_len as u32).to_le_bytes()); // p_memsz
        bytes[ph1 + 24..ph1 + 28].copy_from_slice(&4u32.to_le_bytes()); // p_flags = R
        bytes[ph1 + 28..ph1 + 32].copy_from_slice(&4u32.to_le_bytes()); // p_align
                                                                        // dynamic entries
        for (index, &(tag, value)) in entries.iter().enumerate() {
            let at = DYN_OFF + index * 8;
            bytes[at..at + 4].copy_from_slice(&tag.to_le_bytes());
            bytes[at + 4..at + 8].copy_from_slice(&(value as u32).to_le_bytes());
        }
        // dynstr
        bytes[str_off..str_off + strsz].copy_from_slice(&dynstr);
        bytes
    }

    const DYN_OFF: usize = 52 + 2 * 32;
    const ELF32_EHDR_SIZE: usize = 52;
    const ET_DYN: u16 = 3;
    const EM_ARM: u16 = 40;
    const DT_STRTAB: u32 = 5;
    const DT_STRSZ: u32 = 10;
    const DT_NEEDED: u32 = 1;
    const DT_SONAME: u32 = 14;

    /// Copy `path` into a NUL-terminated stack buffer: the VFS syscall
    /// helpers take raw C paths, and a Rust `&str` is not NUL-terminated.
    fn c_path<const N: usize>(path: &str) -> [core::ffi::c_char; N] {
        assert!(path.len() < N, "test path too long: {path}");
        let mut buffer = [0 as core::ffi::c_char; N];
        for (byte, slot) in path.bytes().zip(buffer.iter_mut()) {
            *slot = byte as core::ffi::c_char;
        }
        buffer
    }

    fn write_file(path: &str, bytes: &[u8]) {
        let c_path = c_path::<64>(path);
        let fd = crate::vfs::syscalls::open(
            c_path.as_ptr(),
            libc::O_CREAT | libc::O_WRONLY | libc::O_TRUNC,
            0o644,
        );
        assert!(fd > 0, "open {path} for write: {fd}");
        let wrote = crate::vfs::syscalls::write(fd, bytes.as_ptr(), bytes.len());
        assert_eq!(wrote as usize, bytes.len(), "write {path}");
        crate::vfs::syscalls::close(fd);
    }

    fn make_dir(path: &str) {
        let c_path = c_path::<64>(path);
        let rc = crate::vfs::syscalls::mkdir(c_path.as_ptr(), 0o755);
        // Tests share the root tmpfs; a directory a previous test seeded is
        // fine to reuse, exactly as the boot seeder tolerates EEXIST.
        assert!(rc == 0 || rc == -libc::EEXIST, "mkdir {path}: {rc}");
    }

    /// Remove a file, tolerating ENOENT (a fresh tmpfs never had it).
    fn remove_file(path: &str) {
        let c_path = c_path::<64>(path);
        let rc = crate::vfs::syscalls::unlink(c_path.as_ptr());
        assert!(rc == 0 || rc == -libc::ENOENT, "unlink {path}: {rc}");
    }

    fn namespace_at(pwd: &str, launch: &str) -> ApplicationNamespace {
        ApplicationNamespace::from_launch_path(
            launch,
            pwd,
            crate::application::board_dynamic_profile(),
        )
        .expect("namespace")
    }

    fn seed_layout() {
        make_dir("/apps");
        make_dir("/apps/hello");
        make_dir("/apps/hello/lib");
        make_dir("/system");
        make_dir("/system/lib");
        // Tests share the tmpfs: clear any leftovers earlier tests planted in
        // the private lib dir, so plain-name resolution starts from a clean
        // slate.
        remove_file("/apps/hello/lib/libsys_extra.so.1");
        remove_file("/apps/hello/lib/libmissing.so.1");
        // The root: needs a private DSO by plain name and the system libc.
        write_file(
            "/apps/hello/app.elf",
            &dso_elf(&["libfoo.so.1", "libc.so.1"], Some("app.elf")),
        );
        // The private DSO: no SONAME, plain-name request only.
        write_file("/apps/hello/lib/libfoo.so.1", &dso_elf(&[], None));
        // The system DSOs.
        write_file("/system/lib/libc.so.1", &dso_elf(&[], Some("libc.so.1")));
        write_file(
            "/system/lib/libsys_extra.so.1",
            &dso_elf(&[], Some("libsys_extra.so.1")),
        );
    }

    /// Plan the hello layout and assert the BFS closure, edges and system
    /// keys (paths matrix).
    #[test]
    fn plan_walks_private_then_system_closure() {
        seed_layout();
        let namespace = namespace_at("/apps/hello", "app.elf");
        let planner = NamespaceLoadPlanner::new(&namespace, &TEST_CATALOG, SessionLimits::DEFAULT);
        let plan = planner.plan().expect("plan");

        // root, private DSO, system DSO
        assert_eq!(plan.images().len(), 3);
        assert_eq!(plan.images()[0].path(), "/apps/hello/app.elf");
        assert!(!plan.images()[0].system());
        assert_eq!(plan.images()[1].path(), "/apps/hello/lib/libfoo.so.1");
        assert!(!plan.images()[1].system());
        assert_eq!(plan.images()[2].path(), "/system/lib/libc.so.1");
        assert!(plan.images()[2].system());

        // Edges: root→libfoo (plain name, private hit), root→libc (plain
        // name, catalog fallback).
        assert_eq!(plan.edges().len(), 2);
        assert_eq!(plan.edges()[0].requester(), 0);
        assert_eq!(plan.edges()[0].provider(), 1);
        assert_eq!(plan.edges()[1].requester(), 0);
        assert_eq!(plan.edges()[1].provider(), 2);

        // System keys: sorted, deduplicated, just libc.
        assert_eq!(plan.system_keys().len(), 1);
        assert_eq!(plan.system_keys()[0].as_bytes(), b"/system/lib/libc.so.1");

        // The scanned SONAME came through.
        assert_eq!(
            plan.images()[0]
                .scanned()
                .declared_soname
                .as_ref()
                .unwrap()
                .as_bytes(),
            b"app.elf"
        );
        assert!(plan.images()[1].scanned().declared_soname.is_none());
    }

    /// A relative DT_NEEDED from the root resolves against the requester
    /// ELF's directory.
    #[test]
    fn plan_resolves_relative_needed_against_requester_dir() {
        seed_layout();
        // root needs "./lib/libfoo.so.1" by relative path.
        write_file(
            "/apps/hello/app.elf",
            &dso_elf(&["./lib/libfoo.so.1"], Some("app.elf")),
        );
        let namespace = namespace_at("/apps/hello", "app.elf");
        let planner = NamespaceLoadPlanner::new(&namespace, &TEST_CATALOG, SessionLimits::DEFAULT);
        let plan = planner.plan().expect("plan");
        assert_eq!(plan.images().len(), 2);
        assert_eq!(plan.images()[1].path(), "/apps/hello/lib/libfoo.so.1");
        assert!(plan.system_keys().is_empty());
    }

    /// An absolute `DT_NEEDED` that equals a catalog path is a system DSO.
    #[test]
    fn plan_treats_catalog_path_needed_as_system() {
        seed_layout();
        write_file(
            "/apps/hello/app.elf",
            &dso_elf(&["/system/lib/libc.so.1"], Some("app.elf")),
        );
        let namespace = namespace_at("/apps/hello", "app.elf");
        let planner = NamespaceLoadPlanner::new(&namespace, &TEST_CATALOG, SessionLimits::DEFAULT);
        let plan = planner.plan().expect("plan");
        assert_eq!(plan.images().len(), 2);
        assert!(plan.images()[1].system());
        assert_eq!(plan.system_keys()[0].as_bytes(), b"/system/lib/libc.so.1");
    }

    /// A plain-name request whose private file is missing falls back to the
    /// catalog.
    #[test]
    fn plan_falls_back_to_catalog_when_private_missing() {
        seed_layout();
        write_file(
            "/apps/hello/app.elf",
            &dso_elf(&["libsys_extra.so.1"], Some("app.elf")),
        );
        // Ensure no private copy shadows the name: a leftover garbage file
        // from an earlier test would make the plan fail on it instead.
        remove_file("/apps/hello/lib/libsys_extra.so.1");
        let namespace = namespace_at("/apps/hello", "app.elf");
        let planner = NamespaceLoadPlanner::new(&namespace, &TEST_CATALOG, SessionLimits::DEFAULT);
        let plan = planner.plan().expect("plan");
        assert_eq!(plan.images().len(), 2);
        assert_eq!(plan.images()[1].path(), "/system/lib/libsys_extra.so.1");
        assert!(plan.images()[1].system());
        assert_eq!(
            plan.system_keys()[0].as_bytes(),
            b"/system/lib/libsys_extra.so.1"
        );
    }

    /// A plain-name request whose private file is present but broken fails
    /// without falling back.
    #[test]
    fn plan_broken_private_file_does_not_fall_back() {
        seed_layout();
        write_file(
            "/apps/hello/app.elf",
            &dso_elf(&["libsys_extra.so.1"], Some("app.elf")),
        );
        // A garbage private file shadows the catalog entry by name.
        write_file("/apps/hello/lib/libsys_extra.so.1", &[0u8; 16]);
        let namespace = namespace_at("/apps/hello", "app.elf");
        let planner = NamespaceLoadPlanner::new(&namespace, &TEST_CATALOG, SessionLimits::DEFAULT);
        let result = planner.plan();
        assert!(
            result.is_err(),
            "a present-but-broken private DSO must fail the plan without catalog fallback"
        );
    }

    /// A plain-name request resolved nowhere is unresolved.
    #[test]
    fn plan_unresolved_plain_name_fails() {
        seed_layout();
        write_file(
            "/apps/hello/app.elf",
            &dso_elf(&["libmissing.so.1"], Some("app.elf")),
        );
        let namespace = namespace_at("/apps/hello", "app.elf");
        let planner = NamespaceLoadPlanner::new(&namespace, &TEST_CATALOG, SessionLimits::DEFAULT);
        let result = planner.plan();
        assert!(
            result.is_err(),
            "an unresolvable DT_NEEDED must fail the plan"
        );
    }

    /// The same DSO requested twice is planned only once.
    #[test]
    fn plan_dedups_repeated_requests() {
        seed_layout();
        write_file(
            "/apps/hello/app.elf",
            &dso_elf(&["libc.so.1", "libc.so.1"], Some("app.elf")),
        );
        let namespace = namespace_at("/apps/hello", "app.elf");
        let planner = NamespaceLoadPlanner::new(&namespace, &TEST_CATALOG, SessionLimits::DEFAULT);
        let plan = planner.plan().expect("plan");
        assert_eq!(plan.images().len(), 2);
        assert_eq!(plan.edges().len(), 2);
        // Both edges point at the same provider.
        assert_eq!(plan.edges()[0].provider(), plan.edges()[1].provider());
        assert_eq!(plan.system_keys().len(), 1);
    }

    /// A plain name and an explicit relative path that normalize to the same
    /// VFS path produce two graph edges but only one mapped image.
    #[test]
    fn plan_dedups_lookup_aliases_by_path() {
        seed_layout();
        write_file(
            "/apps/hello/app.elf",
            &dso_elf(&["libfoo.so.1", "./lib/libfoo.so.1"], Some("app.elf")),
        );
        let namespace = namespace_at("/apps/hello", "app.elf");
        let planner = NamespaceLoadPlanner::new(&namespace, &TEST_CATALOG, SessionLimits::DEFAULT);
        let plan = planner.plan().expect("plan");
        assert_eq!(plan.images().len(), 2);
        assert_eq!(plan.edges().len(), 2);
        assert_eq!(plan.edges()[0].provider(), plan.edges()[1].provider());
    }
}
