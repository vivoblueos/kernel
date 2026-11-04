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

//! Content fingerprints and recoverable publication for a checkout's crates.

use anyhow::{bail, ensure, Context, Result};
use fs2::FileExt;
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use std::collections::{BTreeMap, BTreeSet};
use std::fs::{self, File, OpenOptions};
use std::io::{Read, Write};
use std::path::{Component, Path, PathBuf};
use std::process::{Command, Stdio};

/// The current synchronization record format version.
pub const STATE_VERSION: u32 = 1;

/// The filename of the stored synchronization record.
pub const STATE_FILE: &str = "gnrt_sync_state.json";

/// The filename of the marker for an unfinished publication.
pub const TRANSACTION_FILE: &str = ".gnrt-sync-in-progress.json";

/// A content fingerprint for a file or directory.
#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub struct FileRecord {
    /// The checkout-relative path, or an absolute path outside the checkout.
    pub path: String,
    /// Whether the path identifies a file or directory.
    pub kind: String,
    /// The SHA-256 fingerprint of the file or directory contents.
    pub sha256: String,
}

/// A scoped synchronization request covered by a synchronization record.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct RequestRecord {
    /// The GN entry label used by the request.
    pub target: String,
    /// The normalized GN arguments used by the request.
    pub args: String,
    /// The effective GN arguments recorded after collection.
    pub effective_args: BTreeMap<String, String>,
    /// The declaration labels covered by the request.
    pub roots: Vec<String>,
    /// The content fingerprints used by the request.
    pub inputs: Vec<FileRecord>,
}

/// The validated synchronization record for a checkout.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct SyncState {
    /// The serialization format version.
    pub version: u32,
    /// Whether the record covers the complete declaration catalog.
    pub complete: bool,
    /// The SHA-256 fingerprint of the resolved declaration catalog.
    pub catalog_sha256: String,
    /// The declaration roots covered by the record.
    pub roots: Vec<String>,
    /// The files and directories that determined the synchronization outputs.
    pub inputs: Vec<FileRecord>,
    /// The generated and vendored outputs covered by the record.
    pub artifacts: Vec<FileRecord>,
    /// The relevant environment values recorded during sync.
    pub environment: BTreeMap<String, Option<String>>,
    /// The tool executables and their content fingerprints.
    pub tools: BTreeMap<String, FileRecord>,
    /// The scoped synchronization requests recorded by this record.
    pub requests: Vec<RequestRecord>,
}

impl SyncState {
    /// Reads a synchronization record without accepting incompatible versions.
    ///
    /// # Errors
    ///
    /// Returns an error for unreadable, malformed, or incompatible records.
    pub fn read(path: &Path) -> Result<Self> {
        let state: Self = serde_json::from_slice(&fs::read(path)?).with_context(|| {
            format!(
                "gnrt could not load the synchronization record at {}.",
                path.display()
            )
        })?;
        ensure!(
            state.version == STATE_VERSION,
            "The synchronization record uses an unsupported format version."
        );
        Ok(state)
    }

    /// Checks generation inputs, tool bindings, environment, and all artifacts.
    ///
    /// # Errors
    ///
    /// Returns an error identifying a missing or changed input or artifact.
    pub fn validate(&self, root: &Path) -> Result<()> {
        self.validate_inputs(root)?;
        for record in &self.artifacts {
            validate_record(root, record)?;
        }
        Ok(())
    }

    /// Checks generation inputs without requiring outputs to be complete.
    ///
    /// # Errors
    ///
    /// Returns an error when inputs, environment, or tool bindings changed.
    pub fn validate_inputs(&self, root: &Path) -> Result<()> {
        for record in &self.inputs {
            validate_record(root, record)?;
        }
        // Scoped requests share outputs; a changed request invalidates the record.
        if !self.complete {
            for request in &self.requests {
                for record in &request.inputs {
                    validate_record(root, record)?;
                }
            }
        }
        for (name, value) in &self.environment {
            ensure!(
                environment_value(root, name) == *value,
                "The value of environment variable {name} has changed since the previous synchronization."
            );
        }
        for (name, record) in &self.tools {
            let executable = tool_path(name)?;
            let current = fingerprint(root, &executable)?;
            ensure!(
                current == *record,
                "The {name} executable has changed since the previous synchronization."
            );
        }
        Ok(())
    }

    /// Finds an unchanged request already covered by this record.
    ///
    /// The request must match the target and normalized arguments, and its
    /// declaration roots and input fingerprints must remain covered and valid.
    pub fn request(&self, root: &Path, target: &str, args: &str) -> Option<&RequestRecord> {
        self.requests.iter().find(|request| {
            request.target == target
                && request.args == args
                && request.roots.iter().all(|label| self.roots.contains(label))
                && request
                    .inputs
                    .iter()
                    .all(|input| validate_record(root, input).is_ok())
        })
    }
}

/// SHA-256 of `bytes`, encoded consistently with the offline checker.
pub fn digest(bytes: &[u8]) -> String {
    format!("{:x}", Sha256::digest(bytes))
}

/// Hashes a file without loading its entire contents into memory.
fn file_digest(path: &Path) -> Result<String> {
    let mut file = File::open(path)
        .with_context(|| format!("gnrt could not read the file at {}.", path.display()))?;
    let mut hasher = Sha256::new();
    let mut buffer = [0; 64 * 1024];
    loop {
        let count = file.read(&mut buffer)?;
        if count == 0 {
            break;
        }
        hasher.update(&buffer[..count]);
    }
    Ok(format!("{:x}", hasher.finalize()))
}

/// Identifies metadata and build outputs excluded from directory fingerprints.
fn ignored_name(name: &str) -> bool {
    name == ".git" || name == ".gnrt.lock" || name.ends_with(".build_script_outputs.stamp")
}

/// Collects relative paths and content digests for a directory tree.
fn tree_entries(root: &Path, dir: &Path, entries: &mut Vec<(String, String)>) -> Result<()> {
    for entry in fs::read_dir(dir)? {
        let entry = entry?;
        let path = entry.path();
        if ignored_name(&entry.file_name().to_string_lossy()) {
            continue;
        }
        let relative = path
            .strip_prefix(root)?
            .to_string_lossy()
            .replace('\\', "/");
        if entry.file_type()?.is_symlink() {
            entries.push((
                relative,
                digest(format!("symlink:{}", fs::read_link(path)?.display()).as_bytes()),
            ));
        } else if path.is_dir() {
            tree_entries(root, &path, entries)?;
        } else if path.is_file() {
            entries.push((relative, file_digest(&path)?));
        }
    }
    Ok(())
}

/// Hashes a directory tree in deterministic path order.
fn tree_digest(path: &Path) -> Result<String> {
    let mut entries = Vec::new();
    tree_entries(path, path, &mut entries)?;
    entries.sort();
    let mut hasher = Sha256::new();
    for (name, digest) in entries {
        hasher.update(name.as_bytes());
        hasher.update([0]);
        hasher.update(digest.as_bytes());
        hasher.update([0]);
    }
    Ok(format!("{:x}", hasher.finalize()))
}

/// Fingerprints a file or a recursively declared directory input.
///
/// # Errors
///
/// Returns an error when the path is missing or cannot be read.
pub fn fingerprint(root: &Path, path: &Path) -> Result<FileRecord> {
    let path = if path.is_absolute() {
        path.to_path_buf()
    } else {
        root.join(path)
    };
    let canonical = path.canonicalize().with_context(|| {
        format!(
            "The synchronization input at {} is missing or cannot be accessed.",
            path.display()
        )
    })?;
    let canonical_root = root.canonicalize()?;
    let stored = canonical
        .strip_prefix(&canonical_root)
        .unwrap_or(&canonical);
    let is_directory = canonical.is_dir();
    Ok(FileRecord {
        path: stored.to_string_lossy().replace('\\', "/"),
        kind: if is_directory { "directory" } else { "file" }.to_owned(),
        sha256: if is_directory {
            tree_digest(&canonical)?
        } else {
            file_digest(&canonical)?
        },
    })
}

/// Collects a deterministic fingerprint list without duplicate paths.
///
/// # Errors
///
/// Returns an error when an input cannot be read.
pub fn fingerprints(
    root: &Path,
    paths: impl IntoIterator<Item = PathBuf>,
) -> Result<Vec<FileRecord>> {
    let mut records = BTreeMap::new();
    for path in paths {
        let record = fingerprint(root, &path)?;
        records.insert(record.path.clone(), record);
    }
    Ok(records.into_values().collect())
}

/// Checks one recorded input, preserving its logical name in diagnostics.
///
/// # Errors
///
/// Returns an error when its content or path no longer matches.
pub fn validate_record(root: &Path, record: &FileRecord) -> Result<()> {
    let current = fingerprint(root, &root.join(&record.path))?;
    ensure!(
        current == *record,
        "The recorded file or directory at {} has changed since the previous synchronization.",
        record.path
    );
    Ok(())
}

/// Records a relevant environment value without the checkout's absolute path.
pub fn environment_value(root: &Path, name: &str) -> Option<String> {
    std::env::var(name).ok().map(|value| {
        let root_name = root.to_string_lossy();
        value.replace(root_name.as_ref(), "${GNRT_ROOT}")
    })
}

/// Locates a tool with gnrt-specific overrides for Cargo and GN.
///
/// # Errors
///
/// Returns an error when the executable cannot be found.
pub fn tool_path(name: &str) -> Result<PathBuf> {
    let variable = match name {
        "cargo" => Some("GNRT_CARGO_BIN"),
        "gn" => Some("GNRT_GN_BIN"),
        "rustc" => Some("GNRT_RUSTC_BIN"),
        _ => None,
    };
    if let Some(value) = variable.and_then(std::env::var_os) {
        let value = PathBuf::from(value);
        if value.is_file() {
            return Ok(value);
        }
        if value.components().count() > 1 {
            bail!(
                "gnrt could not find the configured {name} executable at {}.",
                value.display()
            );
        }
        return find_on_path(&value.to_string_lossy());
    }
    find_on_path(name)
}

/// Resolves an explicit executable path or a name from PATH.
fn find_on_path(name: &str) -> Result<PathBuf> {
    if Path::new(name).is_file() {
        return Ok(PathBuf::from(name));
    }
    let search = std::env::var_os("PATH").context("The PATH environment variable is not set.")?;
    std::env::split_paths(&search)
        .map(|dir| dir.join(name))
        .find(|candidate| candidate.is_file())
        .with_context(|| format!("gnrt could not find the {name} executable in PATH."))
}

/// Canonicalizes GN argument source using GN's formatter, without evaluating it.
///
/// # Errors
///
/// Returns an error when GN cannot format the argument source.
pub fn normalize_args(args: &[String]) -> Result<String> {
    let source = args.join(" ");
    if source.trim().is_empty() {
        return Ok(String::new());
    }
    let mut child = Command::new(tool_path("gn")?)
        .args(["format", "--stdin"])
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()?;
    child
        .stdin
        .take()
        .context("gnrt could not access the standard input of the GN formatting process.")?
        .write_all(source.as_bytes())?;
    let output = child.wait_with_output()?;
    ensure!(
        output.status.success(),
        "GN could not format the supplied build arguments: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    let formatted = String::from_utf8(output.stdout)?;
    let mut lines = Vec::new();
    let mut skip_value = false;
    for line in formatted.lines() {
        let trimmed = line.trim();
        if skip_value {
            skip_value = false;
            continue;
        }
        if trimmed.starts_with("gnrt_mode =") {
            skip_value = trimmed.ends_with('=');
            continue;
        }
        lines.push(line);
    }
    if lines.is_empty() {
        Ok(String::new())
    } else {
        Ok(format!("{}\n", lines.join("\n")))
    }
}

/// A lock that prevents concurrent dependency updates within a project.
pub struct SyncLock {
    file: File,
}

impl SyncLock {
    /// Serializes modifications to the shared third-party tree.
    ///
    /// # Errors
    ///
    /// Returns an error if the lock cannot be created or acquired.
    pub fn acquire(vendor: &Path) -> Result<Self> {
        fs::create_dir_all(vendor)?;
        let file = OpenOptions::new()
            .create(true)
            .truncate(false)
            .read(true)
            .write(true)
            .open(vendor.join(".gnrt.lock"))?;
        file.lock_exclusive()?;
        Ok(Self { file })
    }
}

impl Drop for SyncLock {
    fn drop(&mut self) {
        let _ = FileExt::unlock(&self.file);
    }
}

/// The previous contents of one publication destination.
#[derive(Debug, Serialize, Deserialize)]
struct UndoEntry {
    destination: PathBuf,
    backup: Option<PathBuf>,
}

/// Backups needed to recover an interrupted publication.
#[derive(Debug, Serialize, Deserialize)]
struct Journal {
    backup_dir: PathBuf,
    entries: Vec<UndoEntry>,
}

/// Writes one file atomically, preserving the timestamp when content is equal.
///
/// # Errors
///
/// Returns an error when the file cannot be written or replaced.
pub fn write_if_changed(path: &Path, bytes: &[u8]) -> Result<()> {
    if fs::read(path).ok().as_deref() == Some(bytes) {
        return Ok(());
    }
    let parent = path
        .parent()
        .context("The output file path has no parent directory.")?;
    fs::create_dir_all(parent)?;
    let mut temporary = tempfile::NamedTempFile::new_in(parent)?;
    temporary.write_all(bytes)?;
    temporary.as_file().sync_all()?;
    temporary.persist(path).map_err(|error| error.error)?;
    Ok(())
}

/// A publication journal whose presence makes native builds reject the tree.
pub struct Publication {
    marker: PathBuf,
    journal: Journal,
    committed: bool,
}

impl Publication {
    /// Starts a transaction before any vendor or generated outputs are changed.
    ///
    /// # Errors
    ///
    /// Returns an error when an older transaction requires recovery or the
    /// journal cannot be created.
    pub fn begin(vendor: &Path) -> Result<Self> {
        let marker = vendor.join(TRANSACTION_FILE);
        ensure!(!marker.exists(), "A previous synchronization is incomplete. Run `gnrt sync --all` to recover before updating dependency files.");
        let backup = tempfile::Builder::new()
            .prefix(".gnrt-publish-")
            .tempdir_in(vendor)?;
        let journal = Journal {
            backup_dir: backup.into_path(),
            entries: Vec::new(),
        };
        let publication = Self {
            marker,
            journal,
            committed: false,
        };
        publication.save()?;
        Ok(publication)
    }

    /// Persists the recovery journal before destinations are changed.
    fn save(&self) -> Result<()> {
        write_if_changed(&self.marker, &serde_json::to_vec_pretty(&self.journal)?)
    }

    /// Records a destination once before its first modification.
    fn backup(&mut self, path: &Path) -> Result<()> {
        if self
            .journal
            .entries
            .iter()
            .any(|entry| entry.destination == path)
        {
            return Ok(());
        }
        let backup = if path.is_file() {
            let copy = self
                .journal
                .backup_dir
                .join(self.journal.entries.len().to_string());
            fs::copy(path, &copy)?;
            Some(copy)
        } else {
            ensure!(
                !path.exists(),
                "The destination path {} exists but does not refer to a regular file.",
                path.display()
            );
            None
        };
        self.journal.entries.push(UndoEntry {
            destination: path.to_path_buf(),
            backup,
        });
        self.save()
    }

    /// Publishes a candidate file after journaling its previous contents.
    ///
    /// # Errors
    ///
    /// Returns an error if backup or publication fails.
    pub fn write(&mut self, destination: &Path, bytes: &[u8]) -> Result<()> {
        if fs::read(destination).ok().as_deref() == Some(bytes) {
            return Ok(());
        }
        self.backup(destination)?;
        write_if_changed(destination, bytes)
    }

    /// Removes an obsolete generated file after journaling it.
    ///
    /// # Errors
    ///
    /// Returns an error if backup or removal fails.
    pub fn remove(&mut self, destination: &Path) -> Result<()> {
        if destination.is_file() {
            self.backup(destination)?;
            fs::remove_file(destination)?;
        }
        Ok(())
    }

    /// Writes the synchronization record last, then marks the transaction complete.
    ///
    /// # Errors
    ///
    /// Returns an error if the synchronization record or transaction marker cannot be updated.
    pub fn commit(mut self, destination: &Path, state: &SyncState) -> Result<()> {
        self.write(destination, &serde_json::to_vec_pretty(state)?)?;
        fs::remove_file(&self.marker)?;
        self.committed = true;
        fs::remove_dir_all(&self.journal.backup_dir)?;
        Ok(())
    }
}

impl Drop for Publication {
    fn drop(&mut self) {
        if !self.committed {
            log::warn!(
                "gnrt did not finish updating the generated files. Run `gnrt sync --all` to recover the interrupted synchronization before building the project."
            );
        }
    }
}

/// Restores file backups and removes the synchronization record after an
/// interrupted update.
///
/// # Errors
///
/// Returns an error if an interrupted publication cannot be restored.
pub fn recover(vendor: &Path) -> Result<()> {
    let marker = vendor.join(TRANSACTION_FILE);
    if !marker.exists() {
        return Ok(());
    }
    let journal: Journal = serde_json::from_slice(&fs::read(&marker)?)?;
    for entry in journal.entries.iter().rev() {
        match &entry.backup {
            Some(backup) => write_if_changed(&entry.destination, &fs::read(backup)?)?,
            None if entry.destination.exists() => fs::remove_file(&entry.destination)?,
            None => {}
        }
    }
    // Vendor may have been interrupted before the candidate rules existed.
    let state = vendor.join(STATE_FILE);
    if state.exists() {
        fs::remove_file(state)?;
    }
    fs::remove_file(&marker)?;
    fs::remove_dir_all(&journal.backup_dir)?;
    Ok(())
}

/// Validates that a staged output remains inside the checkout.
///
/// # Errors
///
/// Returns an error for absolute paths or paths containing parent traversal.
pub fn validate_destination(path: &Path) -> Result<()> {
    ensure!(
        !path.is_absolute(),
        "The generated file path must be relative to the project root."
    );
    ensure!(
        path.components()
            .all(|component| matches!(component, Component::Normal(_) | Component::CurDir)),
        "The generated file path {} must not contain '..' or a filesystem prefix.",
        path.display()
    );
    Ok(())
}

/// Returns an ordered set of root labels from collected declarations.
pub fn root_labels(declarations: &crate::collect::DeclarationGroups) -> BTreeSet<String> {
    declarations
        .cargo
        .iter()
        .filter_map(|declaration| match declaration {
            crate::collect::Declaration::Crate(spec) => Some(spec.label.clone()),
            _ => None,
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn sync_lock_excludes_another_writer_until_released() {
        let directory = tempfile::tempdir().unwrap();
        let lock = SyncLock::acquire(directory.path()).unwrap();
        let contender = OpenOptions::new()
            .read(true)
            .write(true)
            .open(directory.path().join(".gnrt.lock"))
            .unwrap();
        assert!(FileExt::try_lock_exclusive(&contender).is_err());
        drop(lock);
        FileExt::try_lock_exclusive(&contender).unwrap();
        FileExt::unlock(&contender).unwrap();
    }

    #[test]
    fn content_validation_ignores_timestamp_and_detects_directory_changes() {
        let dir = tempfile::tempdir().unwrap();
        let source = dir.path().join("crate");
        fs::create_dir(&source).unwrap();
        fs::write(source.join("lib.rs"), "one").unwrap();
        let record = fingerprint(dir.path(), &source).unwrap();
        fs::write(source.join("lib.rs"), "one").unwrap();
        validate_record(dir.path(), &record).unwrap();
        fs::write(source.join("new.rs"), "two").unwrap();
        assert!(validate_record(dir.path(), &record).is_err());
        fs::remove_file(source.join("new.rs")).unwrap();
        fs::remove_file(source.join("lib.rs")).unwrap();
        assert!(validate_record(dir.path(), &record).is_err());
    }

    #[test]
    fn interrupted_publication_restores_previous_rules_and_invalidates_sync_record() {
        let dir = tempfile::tempdir().unwrap();
        let existing = dir.path().join("BUILD.gn");
        let created = dir.path().join("index.json");
        fs::write(&existing, "old").unwrap();
        fs::write(dir.path().join(STATE_FILE), "old sync record").unwrap();
        {
            let mut transaction = Publication::begin(dir.path()).unwrap();
            transaction.write(&existing, b"new").unwrap();
            transaction.write(&created, b"new").unwrap();
        }
        assert!(dir.path().join(TRANSACTION_FILE).exists());
        recover(dir.path()).unwrap();
        assert_eq!(fs::read_to_string(existing).unwrap(), "old");
        assert!(!created.exists());
        assert!(!dir.path().join(STATE_FILE).exists());
        assert!(!dir.path().join(TRANSACTION_FILE).exists());
    }

    #[test]
    fn staged_destinations_cannot_escape_checkout() {
        assert!(validate_destination(Path::new("third_party/.gnrt/lib/BUILD.gn")).is_ok());
        assert!(validate_destination(Path::new("../Cargo.lock")).is_err());
        assert!(validate_destination(Path::new("/tmp/BUILD.gn")).is_err());
    }
}
