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

//! Artifact identity and resolver contract for [`DynamicLinker`](super::DynamicLinker).
//!
//! The resolver is deliberately free of any VFS, environment variable, current
//! directory, or `librs` dependency: it answers a [`DependencyRequest`] from a
//! catalog of resolved artifacts. The kernel application layer
//! adapts the same contract to VFS paths and the system DSO registry.

use alloc::vec::Vec;

use crate::{
    error::{LoadError, LoadErrorKind, LoadResult},
    reader::ElfReader,
};

/// Opaque, comparable file identity supplied by the artifact backend.
///
/// Two [`FileIdentity`] values compare equal only when they refer to the same
/// backend artifact. The loader does not interpret the identity bytes.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct FileIdentity {
    bytes: Vec<u8>,
}

impl FileIdentity {
    #[inline]
    pub fn from_bytes(bytes: &[u8]) -> Self {
        Self {
            bytes: bytes.into(),
        }
    }

    fn try_clone(&self) -> LoadResult<Self> {
        Ok(Self {
            bytes: try_copy_bytes(&self.bytes)?,
        })
    }

    fn metadata_bytes(&self) -> u64 {
        self.bytes.len() as u64
    }
}

/// How one artifact participates in a link session.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ArtifactRole {
    /// The link root: must carry a canonical entry fully inside an executable
    /// region and is published as the application entry.
    ExecutableRoot,
    /// A dependent shared object: may have `e_entry == 0` and may omit
    /// `DT_SONAME` (two SONAME-less files are distinguished by identity and
    /// path at the resolver layer).
    SharedObject,
}

/// Stable identity of one loaded artifact.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct ArtifactIdentity {
    file: FileIdentity,
}

impl ArtifactIdentity {
    #[inline]
    pub const fn new(file: FileIdentity) -> Self {
        Self { file }
    }

    #[inline]
    pub const fn file(&self) -> &FileIdentity {
        &self.file
    }

    pub fn try_clone(&self) -> LoadResult<Self> {
        Ok(Self {
            file: self.file.try_clone()?,
        })
    }

    pub(crate) fn metadata_bytes(&self) -> u64 {
        self.file.metadata_bytes()
    }
}

/// Owned, validated dependency name (a `DT_NEEDED` or `DT_SONAME` value).
///
/// Construction validates that the source bytes form a single NUL-terminated
/// name with no embedded NUL; the stored value is the name without its
/// terminator. First-version comparison is by ELF raw bytes; the resolver's
/// catalog key must canonicalize consistently rather than normalizing case or
/// path separators per layer.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct DependencyName {
    name: Vec<u8>,
}

impl DependencyName {
    /// Validate and copy `bytes`, which must end with exactly one NUL and
    /// contain no other NUL or empty name before it.
    pub fn from_terminated(bytes: &[u8]) -> LoadResult<Self> {
        let name_len = bytes.len().checked_sub(1).filter(|_| {
            bytes.last() == Some(&0) && bytes[..bytes.len() - 1].iter().all(|byte| *byte != 0)
        });
        let Some(name_len) = name_len else {
            return Err(LoadError::new(
                LoadErrorKind::BadElf,
                crate::error::ErrorContext::None,
            ));
        };
        if name_len == 0 {
            return Err(LoadError::new(
                LoadErrorKind::BadElf,
                crate::error::ErrorContext::None,
            ));
        }
        Ok(Self {
            name: try_copy_bytes(&bytes[..name_len])?,
        })
    }

    /// Copy an owned name without requiring a trailing NUL (manifest
    /// catalogs store plain names); rejects empty or NUL-containing bytes.
    pub fn from_bytes(bytes: &[u8]) -> LoadResult<Self> {
        if bytes.is_empty() || bytes.iter().any(|byte| *byte == 0) {
            return Err(LoadError::new(
                LoadErrorKind::BadElf,
                crate::error::ErrorContext::None,
            ));
        }
        Ok(Self {
            name: try_copy_bytes(bytes)?,
        })
    }

    #[inline]
    pub fn as_bytes(&self) -> &[u8] {
        &self.name
    }

    pub(crate) fn try_clone(&self) -> LoadResult<Self> {
        Ok(Self {
            name: try_copy_bytes(&self.name)?,
        })
    }
}

/// The requester of one dependency edge: the graph node asking for a
/// `DT_NEEDED` and the ownership that decides how the resolver may satisfy it.
/// This carries no VFS, path, or registry types into the loader
/// crate — just the session-local image id, its identity and its ownership.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct DependencyRequester<'a> {
    image: ImageId,
    identity: &'a ArtifactIdentity,
    ownership: ImageOwnership,
}

impl<'a> DependencyRequester<'a> {
    #[inline]
    pub const fn new(
        image: ImageId,
        identity: &'a ArtifactIdentity,
        ownership: ImageOwnership,
    ) -> Self {
        Self {
            image,
            identity,
            ownership,
        }
    }

    #[inline]
    pub const fn image(&self) -> ImageId {
        self.image
    }

    #[inline]
    pub const fn identity(&self) -> &ArtifactIdentity {
        self.identity
    }

    #[inline]
    pub const fn ownership(&self) -> ImageOwnership {
        self.ownership
    }
}

/// A request for one `DT_NEEDED` dependency, rooted at its requester.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct DependencyRequest<'a> {
    requester: DependencyRequester<'a>,
    needed: &'a DependencyName,
}

impl<'a> DependencyRequest<'a> {
    #[inline]
    pub const fn new(requester: DependencyRequester<'a>, needed: &'a DependencyName) -> Self {
        Self { requester, needed }
    }

    #[inline]
    pub const fn requester(&self) -> DependencyRequester<'a> {
        self.requester
    }

    #[inline]
    pub const fn needed(&self) -> &DependencyName {
        self.needed
    }
}

/// Whether a resolved artifact is owned by this link session or shared with the
/// system DSO catalog.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ImageOwnership {
    /// Owned by this link session: allocated, relocated and sealed here.
    SessionPrivate,
    /// A candidate to become a shared system DSO, loaded for the first time.
    SystemCandidate,
    /// A Ready system DSO imported from the registry: already relocated and
    /// sealed, contributed to the graph/scopes without a fresh load.
    ExternalReady,
}

/// A resolved artifact: its identity and reader.
pub struct ResolvedArtifact<R> {
    identity: ArtifactIdentity,
    ownership: ImageOwnership,
    reader: R,
}

impl<R> ResolvedArtifact<R> {
    #[inline]
    pub const fn new(identity: ArtifactIdentity, ownership: ImageOwnership, reader: R) -> Self {
        Self {
            identity,
            ownership,
            reader,
        }
    }

    #[inline]
    pub const fn identity(&self) -> &ArtifactIdentity {
        &self.identity
    }

    #[inline]
    pub const fn ownership(&self) -> ImageOwnership {
        self.ownership
    }

    #[inline]
    pub const fn reader(&self) -> &R {
        &self.reader
    }

    #[inline]
    pub fn into_reader(self) -> R {
        self.reader
    }

    #[inline]
    pub fn into_parts(self) -> (ArtifactIdentity, ImageOwnership, R) {
        (self.identity, self.ownership, self.reader)
    }
}

/// Resolves a dependency name to a concrete artifact.
///
/// `resolve` returns either a reader for the returned [`ArtifactIdentity`] (a
/// fresh `Load`) or a Ready provider the
/// registry already relocated and sealed (an `Import`). A failed
/// resolution must leave no loading entry behind.
pub trait ArtifactResolver {
    type Reader: ElfReader;

    fn resolve(
        &mut self,
        request: &DependencyRequest<'_>,
    ) -> LoadResult<DependencyResolution<Self::Reader>>;
}

/// What a [`DependencyRequest`] resolved into.
///
/// `Load` hands the session an artifact reader;
/// `Import` hands it a ready provider already relocated and sealed by a
/// previous link, to be joined to the graph and scopes without a fresh load.
pub enum DependencyResolution<R> {
    Load(ResolvedArtifact<R>),
    Import(super::ImportedImageDescriptor),
}

fn try_copy_bytes(bytes: &[u8]) -> LoadResult<Vec<u8>> {
    let mut copy = Vec::new();
    copy.try_reserve_exact(bytes.len()).map_err(|_| {
        LoadError::new(LoadErrorKind::OutOfMemory, crate::error::ErrorContext::None)
    })?;
    copy.extend_from_slice(bytes);
    Ok(copy)
}

/// Stable identifier of a loaded image within one session.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct ImageId(u32);

impl ImageId {
    #[inline]
    pub const fn new(value: u32) -> Self {
        Self(value)
    }

    #[inline]
    pub const fn get(self) -> u32 {
        self.0
    }
}
