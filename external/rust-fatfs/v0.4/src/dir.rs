#[cfg(all(not(feature = "std"), feature = "alloc", feature = "lfn"))]
use alloc::vec::Vec;
use core::num;
use core::str;
#[cfg(feature = "lfn")]
use core::{iter, slice};

use crate::dir_entry::{
    DirEntry, DirEntryData, DirFileEntryData, DirLfnEntryData, FileAttributes, ShortName, DIR_ENTRY_SIZE,
};
#[cfg(feature = "lfn")]
use crate::dir_entry::{LFN_ENTRY_LAST_FLAG, LFN_PART_LEN};
use crate::dir_entry::{SFN_PADDING, SFN_SIZE};
use crate::error::{Error, IoError};
use crate::file::File;
use crate::fs::{DiskSlice, FileSystem, FsIoAdapter, OemCpConverter, ReadWriteSeek};
use crate::io::{self, IoBase, Read, Seek, SeekFrom, Write};
use crate::time::TimeProvider;

const LFN_PADDING: u16 = 0xFFFF;

pub(crate) enum DirRawStream<'a, IO: ReadWriteSeek, TP, OCC> {
    File(File<'a, IO, TP, OCC>),
    Root(DiskSlice<FsIoAdapter<'a, IO, TP, OCC>, FsIoAdapter<'a, IO, TP, OCC>>),
}

impl<IO: ReadWriteSeek, TP, OCC> DirRawStream<'_, IO, TP, OCC> {
    fn abs_pos(&self) -> Option<u64> {
        match self {
            DirRawStream::File(file) => file.abs_pos(),
            DirRawStream::Root(slice) => Some(slice.abs_pos()),
        }
    }

    fn first_cluster(&self) -> Option<u32> {
        match self {
            DirRawStream::File(file) => file.first_cluster(),
            DirRawStream::Root(_) => None,
        }
    }

    pub(crate) fn is_root_dir(&self) -> bool {
        match self {
            DirRawStream::File(file) => file.is_root_dir(),
            DirRawStream::Root(_) => true,
        }
    }
}

// Note: derive cannot be used because of invalid bounds. See: https://github.com/rust-lang/rust/issues/26925
impl<IO: ReadWriteSeek, TP, OCC> Clone for DirRawStream<'_, IO, TP, OCC> {
    fn clone(&self) -> Self {
        match self {
            DirRawStream::File(file) => DirRawStream::File(file.clone()),
            DirRawStream::Root(raw) => DirRawStream::Root(raw.clone()),
        }
    }
}

impl<IO: ReadWriteSeek, TP, OCC> IoBase for DirRawStream<'_, IO, TP, OCC> {
    type Error = Error<IO::Error>;
}

impl<IO: ReadWriteSeek, TP: TimeProvider, OCC> Read for DirRawStream<'_, IO, TP, OCC> {
    fn read(&mut self, buf: &mut [u8]) -> Result<usize, Self::Error> {
        match self {
            DirRawStream::File(file) => file.read(buf),
            DirRawStream::Root(raw) => raw.read(buf),
        }
    }
}

impl<IO: ReadWriteSeek, TP: TimeProvider, OCC> Write for DirRawStream<'_, IO, TP, OCC> {
    fn write(&mut self, buf: &[u8]) -> Result<usize, Self::Error> {
        match self {
            DirRawStream::File(file) => file.write(buf),
            DirRawStream::Root(raw) => raw.write(buf),
        }
    }
    fn flush(&mut self) -> Result<(), Self::Error> {
        match self {
            DirRawStream::File(file) => file.flush(),
            DirRawStream::Root(raw) => raw.flush(),
        }
    }
}

impl<IO: ReadWriteSeek, TP, OCC> Seek for DirRawStream<'_, IO, TP, OCC> {
    fn seek(&mut self, pos: SeekFrom) -> Result<u64, Self::Error> {
        match self {
            DirRawStream::File(file) => file.seek(pos),
            DirRawStream::Root(raw) => raw.seek(pos),
        }
    }
}

fn split_path(path: &str) -> (&str, Option<&str>) {
    let trimmed_path = path.trim_matches('/');
    trimmed_path.find('/').map_or((trimmed_path, None), |n| {
        (&trimmed_path[..n], Some(&trimmed_path[n + 1..]))
    })
}

enum DirEntryOrShortName<'a, IO: ReadWriteSeek, TP, OCC> {
    DirEntry(DirEntry<'a, IO, TP, OCC>),
    ShortName([u8; SFN_SIZE]),
}

/// A FAT filesystem directory.
///
/// This struct is created by the `open_dir` or `create_dir` methods on `Dir`.
/// The root directory is returned by the `root_dir` method on `FileSystem`.
pub struct Dir<'a, IO: ReadWriteSeek, TP, OCC> {
    stream: DirRawStream<'a, IO, TP, OCC>,
    fs: &'a FileSystem<IO, TP, OCC>,
}

impl<'a, IO: ReadWriteSeek, TP, OCC> Dir<'a, IO, TP, OCC> {
    pub(crate) fn new(stream: DirRawStream<'a, IO, TP, OCC>, fs: &'a FileSystem<IO, TP, OCC>) -> Self {
        Dir { stream, fs }
    }

    /// Creates directory entries iterator.
    #[must_use]
    #[allow(clippy::iter_not_returning_iterator)]
    pub fn iter(&self) -> DirIter<'a, IO, TP, OCC> {
        DirIter::new(self.stream.clone(), self.fs, true)
    }
}

impl<'a, IO: ReadWriteSeek, TP: TimeProvider, OCC: OemCpConverter> Dir<'a, IO, TP, OCC> {
    fn find_entry(
        &self,
        name: &str,
        is_dir: Option<bool>,
        mut short_name_gen: Option<&mut ShortNameGenerator>,
    ) -> Result<DirEntry<'a, IO, TP, OCC>, Error<IO::Error>> {
        for r in self.iter() {
            let e = r?;
            // compare name ignoring case
            if e.eq_name(name) {
                // check if file or directory is expected
                if is_dir.is_some() && Some(e.is_dir()) != is_dir {
                    if e.is_dir() {
                        error!("Is a directory");
                    } else {
                        error!("Not a directory");
                    }
                    return Err(Error::InvalidInput);
                }
                return Ok(e);
            }
            // update short name generator state
            if let Some(ref mut gen) = short_name_gen {
                gen.add_existing(e.raw_short_name());
            }
        }
        Err(Error::NotFound) //("No such file or directory"))
    }

    pub fn contais_entry(&self, name: &str, is_dir: bool) -> Result<bool, Error<IO::Error>> {
        match self.find_entry(name, Some(is_dir), None) {
            Ok(_) => Ok(true),
            Err(Error::NotFound) => Ok(false),
            Err(error) => Err(error),
        }
    }

    #[allow(clippy::type_complexity)]
    pub(crate) fn find_volume_entry(&self) -> Result<Option<DirEntry<'a, IO, TP, OCC>>, Error<IO::Error>> {
        for r in DirIter::new(self.stream.clone(), self.fs, false) {
            let e = r?;
            if e.data.is_volume() {
                return Ok(Some(e));
            }
        }
        Ok(None)
    }

    fn check_for_existence(
        &self,
        name: &str,
        is_dir: Option<bool>,
    ) -> Result<DirEntryOrShortName<'a, IO, TP, OCC>, Error<IO::Error>> {
        let mut short_name_gen = ShortNameGenerator::new(name);
        loop {
            // find matching entry
            let r = self.find_entry(name, is_dir, Some(&mut short_name_gen));
            match r {
                // file not found - continue with short name generation
                Err(Error::NotFound) => {}
                // unexpected error - return it
                Err(err) => return Err(err),
                // directory already exists - return it
                Ok(e) => return Ok(DirEntryOrShortName::DirEntry(e)),
            };
            // try to generate short name
            if let Ok(name) = short_name_gen.generate() {
                return Ok(DirEntryOrShortName::ShortName(name));
            }
            // there were too many collisions in short name generation
            // try different checksum in the next iteration
            short_name_gen.next_iteration();
        }
    }

    /// Opens existing subdirectory.
    ///
    /// `path` is a '/' separated directory path relative to self directory.
    ///
    /// # Errors
    ///
    /// Errors that can be returned:
    ///
    /// * `Error::NotFound` will be returned if `path` does not point to any existing directory entry.
    /// * `Error::InvalidInput` will be returned if `path` points to a file that is not a directory.
    /// * `Error::Io` will be returned if the underlying storage object returned an I/O error.
    pub fn open_dir(&self, path: &str) -> Result<Self, Error<IO::Error>> {
        trace!("Dir::open_dir {}", path);
        let (name, rest_opt) = split_path(path);
        let e = self.find_entry(name, Some(true), None)?;
        match rest_opt {
            Some(rest) => e.to_dir().open_dir(rest),
            None => Ok(e.to_dir()),
        }
    }

    /// Opens existing file.
    ///
    /// `path` is a '/' separated file path relative to self directory.
    ///
    /// # Errors
    ///
    /// Errors that can be returned:
    ///
    /// * `Error::NotFound` will be returned if `path` points to a non-existing directory entry.
    /// * `Error::InvalidInput` will be returned if `path` points to a file that is a directory.
    /// * `Error::Io` will be returned if the underlying storage object returned an I/O error.
    pub fn open_file(&self, path: &str) -> Result<File<'a, IO, TP, OCC>, Error<IO::Error>> {
        trace!("Dir::open_file {}", path);
        // traverse path
        let (name, rest_opt) = split_path(path);
        if let Some(rest) = rest_opt {
            let e = self.find_entry(name, Some(true), None)?;
            return e.to_dir().open_file(rest);
        }
        // convert entry to a file
        let e = self.find_entry(name, Some(false), None)?;
        Ok(e.to_file())
    }

    /// Creates new or opens existing file=.
    ///
    /// `path` is a '/' separated file path relative to `self` directory.
    /// File is never truncated when opening. It can be achieved by calling `File::truncate` method after opening.
    ///
    /// # Errors
    ///
    /// Errors that can be returned:
    ///
    /// * `Error::InvalidInput` will be returned if `path` points to an existing file that is a directory.
    /// * `Error::InvalidFileNameLength` will be returned if the file name is empty or if it is too long.
    /// * `Error::UnsupportedFileNameCharacter` will be returned if the file name contains an invalid character.
    /// * `Error::NotEnoughSpace` will be returned if there is not enough free space to create a new file.
    /// * `Error::Io` will be returned if the underlying storage object returned an I/O error.
    pub fn create_file(&self, path: &str) -> Result<File<'a, IO, TP, OCC>, Error<IO::Error>> {
        trace!("Dir::create_file {}", path);
        // traverse path
        let (name, rest_opt) = split_path(path);
        if let Some(rest) = rest_opt {
            return self.find_entry(name, Some(true), None)?.to_dir().create_file(rest);
        }
        // this is final filename in the path
        let r = self.check_for_existence(name, Some(false))?;
        match r {
            // file does not exist - create it
            DirEntryOrShortName::ShortName(short_name) => {
                let sfn_entry = self.create_sfn_entry(short_name, FileAttributes::from_bits_truncate(0), None);
                Ok(self.write_entry(name, sfn_entry)?.to_file())
            }
            // file already exists - return it
            DirEntryOrShortName::DirEntry(e) => Ok(e.to_file()),
        }
    }

    /// Creates new directory or opens existing.
    ///
    /// `path` is a '/' separated path relative to self directory.
    ///
    /// # Errors
    ///
    /// Errors that can be returned:
    ///
    /// * `Error::InvalidInput` will be returned if `path` points to an existing file that is not a directory.
    /// * `Error::InvalidFileNameLength` will be returned if the file name is empty or if it is too long.
    /// * `Error::UnsupportedFileNameCharacter` will be returned if the file name contains an invalid character.
    /// * `Error::NotEnoughSpace` will be returned if there is not enough free space to create a new directory.
    /// * `Error::Io` will be returned if the underlying storage object returned an I/O error.
    pub fn create_dir(&self, path: &str) -> Result<Self, Error<IO::Error>> {
        trace!("Dir::create_dir {}", path);
        // traverse path
        let (name, rest_opt) = split_path(path);
        if let Some(rest) = rest_opt {
            return self.find_entry(name, Some(true), None)?.to_dir().create_dir(rest);
        }
        // this is final filename in the path
        let r = self.check_for_existence(name, Some(true))?;
        match r {
            // directory does not exist - create it
            DirEntryOrShortName::ShortName(short_name) => {
                // alloc cluster for directory data
                let cluster = self.fs.alloc_cluster(None, true)?;
                // create entry in parent directory
                let sfn_entry = self.create_sfn_entry(short_name, FileAttributes::DIRECTORY, Some(cluster));
                let entry = self.write_entry(name, sfn_entry)?;
                let dir = entry.to_dir();
                // create special entries "." and ".."
                let dot_sfn = ShortNameGenerator::generate_dot();
                let sfn_entry = self.create_sfn_entry(dot_sfn, FileAttributes::DIRECTORY, entry.first_cluster());
                dir.write_entry(".", sfn_entry)?;
                let dotdot_sfn = ShortNameGenerator::generate_dotdot();
                // cluster of the root dir shall be set to 0 in directory entries.
                let dotdot_cluster = if self.stream.is_root_dir() {
                    None
                } else {
                    self.stream.first_cluster()
                };
                let sfn_entry = self.create_sfn_entry(dotdot_sfn, FileAttributes::DIRECTORY, dotdot_cluster);
                dir.write_entry("..", sfn_entry)?;
                Ok(dir)
            }
            // directory already exists - return it
            DirEntryOrShortName::DirEntry(e) => Ok(e.to_dir()),
        }
    }

    fn is_empty(&self) -> Result<bool, Error<IO::Error>> {
        trace!("Dir::is_empty");
        // check if directory contains no files
        for r in self.iter() {
            let e = r?;
            let name = e.short_file_name_as_bytes();
            // ignore special entries "." and ".."
            if name != b"." && name != b".." {
                return Ok(false);
            }
        }
        Ok(true)
    }

    /// Removes existing file or directory.
    ///
    /// `path` is a '/' separated file path relative to self directory.
    /// Make sure there is no reference to this file (no File instance) or filesystem corruption
    /// can happen.
    ///
    /// # Errors
    ///
    /// Errors that can be returned:
    ///
    /// * `Error::NotFound` will be returned if `path` points to a non-existing directory entry.
    /// * `Error::InvalidInput` will be returned if `path` points to a file that is not a directory.
    /// * `Error::DirectoryIsNotEmpty` will be returned if the specified directory is not empty.
    /// * `Error::Io` will be returned if the underlying storage object returned an I/O error.
    pub fn remove(&self, path: &str) -> Result<(), Error<IO::Error>> {
        trace!("Dir::remove {}", path);
        // traverse path
        let (name, rest_opt) = split_path(path);
        if let Some(rest) = rest_opt {
            let e = self.find_entry(name, Some(true), None)?;
            return e.to_dir().remove(rest);
        }
        // in case of directory check if it is empty
        let e = self.find_entry(name, None, None)?;
        if e.is_dir() && !e.to_dir().is_empty()? {
            return Err(Error::DirectoryIsNotEmpty);
        }
        // free data
        if let Some(n) = e.first_cluster() {
            self.fs.free_cluster_chain(n)?;
        }
        // free long and short name entries
        let mut stream = self.stream.clone();
        stream.seek(SeekFrom::Start(e.offset_range.0))?;
        let num = ((e.offset_range.1 - e.offset_range.0) / u64::from(DIR_ENTRY_SIZE)) as usize;
        for _ in 0..num {
            let mut data = DirEntryData::deserialize(&mut stream)?;
            trace!("removing dir entry {:?}", data);
            data.set_deleted();
            stream.seek(SeekFrom::Current(-i64::from(DIR_ENTRY_SIZE)))?;
            data.serialize(&mut stream)?;
        }
        Ok(())
    }

    /// Renames or moves existing file or directory.
    ///
    /// `src_path` is a '/' separated source file path relative to self directory.
    /// `dst_path` is a '/' separated destination file path relative to `dst_dir`.
    /// `dst_dir` can be set to self directory if rename operation without moving is needed.
    /// Make sure there is no reference to this file (no File instance) or filesystem corruption
    /// can happen.
    ///
    /// # Errors
    ///
    /// Errors that can be returned:
    ///
    /// * `Error::NotFound` will be returned if `src_path` points to a non-existing directory entry or if `dst_path`
    ///   stripped from the last component does not point to an existing directory.
    /// * `Error::AlreadyExists` will be returned if `dst_path` points to an existing directory entry.
    /// * `Error::Io` will be returned if the underlying storage object returned an I/O error.
    pub fn rename(&self, src_path: &str, dst_dir: &Dir<IO, TP, OCC>, dst_path: &str) -> Result<(), Error<IO::Error>> {
        trace!("Dir::rename {} {}", src_path, dst_path);
        // traverse source path
        let (src_name, src_rest_opt) = split_path(src_path);
        if let Some(rest) = src_rest_opt {
            let e = self.find_entry(src_name, Some(true), None)?;
            return e.to_dir().rename(rest, dst_dir, dst_path);
        }
        // traverse destination path
        let (dst_name, dst_rest_opt) = split_path(dst_path);
        if let Some(rest) = dst_rest_opt {
            let e = dst_dir.find_entry(dst_name, Some(true), None)?;
            return self.rename(src_path, &e.to_dir(), rest);
        }
        // move/rename file
        self.rename_internal(src_path, dst_dir, dst_path)
    }

    fn rename_internal(
        &self,
        src_name: &str,
        dst_dir: &Dir<IO, TP, OCC>,
        dst_name: &str,
    ) -> Result<(), Error<IO::Error>> {
        trace!("Dir::rename_internal {} {}", src_name, dst_name);
        // find existing file
        let e = self.find_entry(src_name, None, None)?;
        // check if destionation filename is unused
        let r = dst_dir.check_for_existence(dst_name, None)?;
        let short_name = match r {
            // destination file already exist
            DirEntryOrShortName::DirEntry(ref dst_e) => {
                // check if source and destination entry is the same
                if e.is_same_entry(dst_e) {
                    // nothing to do
                    return Ok(());
                }
                // destination file exists and it is not the same as source file - fail
                return Err(Error::AlreadyExists);
            }
            // destionation file does not exist, short name has been generated
            DirEntryOrShortName::ShortName(short_name) => short_name,
        };
        // free long and short name entries
        let mut stream = self.stream.clone();
        stream.seek(SeekFrom::Start(e.offset_range.0))?;
        let num = ((e.offset_range.1 - e.offset_range.0) / u64::from(DIR_ENTRY_SIZE)) as usize;
        for _ in 0..num {
            let mut data = DirEntryData::deserialize(&mut stream)?;
            trace!("removing LFN entry {:?}", data);
            data.set_deleted();
            stream.seek(SeekFrom::Current(-i64::from(DIR_ENTRY_SIZE)))?;
            data.serialize(&mut stream)?;
        }
        // save new directory entry
        let sfn_entry = e.data.renamed(short_name);
        dst_dir.write_entry(dst_name, sfn_entry)?;
        Ok(())
    }

    fn find_free_entries(&self, num_entries: u32) -> Result<DirRawStream<'a, IO, TP, OCC>, Error<IO::Error>> {
        let mut stream = self.stream.clone();
        let mut first_free: u32 = 0;
        let mut num_free: u32 = 0;
        let mut i: u32 = 0;
        loop {
            let raw_entry = DirEntryData::deserialize(&mut stream)?;
            if raw_entry.is_end() {
                // first unused entry - all remaining space can be used
                if num_free == 0 {
                    first_free = i;
                }
                let pos = u64::from(first_free * DIR_ENTRY_SIZE);
                stream.seek(io::SeekFrom::Start(pos))?;
                return Ok(stream);
            } else if raw_entry.is_deleted() {
                // free entry - calculate number of free entries in a row
                if num_free == 0 {
                    first_free = i;
                }
                num_free += 1;
                if num_free == num_entries {
                    // enough space for new file
                    let pos = u64::from(first_free * DIR_ENTRY_SIZE);
                    stream.seek(io::SeekFrom::Start(pos))?;
                    return Ok(stream);
                }
            } else {
                // used entry - start counting from 0
                num_free = 0;
            }
            i += 1;
        }
    }

    fn create_sfn_entry(
        &self,
        short_name: [u8; SFN_SIZE],
        attrs: FileAttributes,
        first_cluster: Option<u32>,
    ) -> DirFileEntryData {
        let mut raw_entry = DirFileEntryData::new(short_name, attrs);
        raw_entry.set_first_cluster(first_cluster, self.fs.fat_type());
        let now = self.fs.options.time_provider.get_current_date_time();
        raw_entry.set_created(now);
        raw_entry.set_accessed(now.date);
        raw_entry.set_modified(now);
        raw_entry
    }

    #[cfg(feature = "lfn")]
    fn encode_lfn_utf16(name: &str) -> LfnBuffer {
        LfnBuffer::from_ucs2_units(name.encode_utf16())
    }
    #[cfg(not(feature = "lfn"))]
    fn encode_lfn_utf16(_name: &str) -> LfnBuffer {
        LfnBuffer {}
    }

    #[allow(clippy::type_complexity)]
    fn alloc_and_write_lfn_entries(
        &self,
        lfn_utf16: &LfnBuffer,
        short_name: &[u8; SFN_SIZE],
    ) -> Result<(DirRawStream<'a, IO, TP, OCC>, u64), Error<IO::Error>> {
        // get short name checksum
        let lfn_chsum = lfn_checksum(short_name);
        // create LFN entries generator
        let lfn_iter = LfnEntriesGenerator::new(lfn_utf16.as_ucs2_units(), lfn_chsum);
        // find space for new entries (multiple LFN entries and 1 SFN entry)
        let num_entries = lfn_iter.len() as u32 + 1;
        let mut stream = self.find_free_entries(num_entries)?;
        let start_pos = stream.seek(io::SeekFrom::Current(0))?;
        // write LFN entries before SFN entry
        for lfn_entry in lfn_iter {
            lfn_entry.serialize(&mut stream)?;
        }
        Ok((stream, start_pos))
    }

    fn alloc_sfn_entry(&self) -> Result<(DirRawStream<'a, IO, TP, OCC>, u64), Error<IO::Error>> {
        let mut stream = self.find_free_entries(1)?;
        let start_pos = stream.seek(io::SeekFrom::Current(0))?;
        Ok((stream, start_pos))
    }

    fn write_entry(
        &self,
        name: &str,
        raw_entry: DirFileEntryData,
    ) -> Result<DirEntry<'a, IO, TP, OCC>, Error<IO::Error>> {
        trace!("Dir::write_entry {}", name);
        // check if name doesn't contain unsupported characters
        validate_long_name(name)?;
        // convert long name to UTF-16
        let lfn_utf16 = Self::encode_lfn_utf16(name);
        // write LFN entries, except for . and .., which need to be at
        // the first two slots and don't need LFNs anyway
        let (mut stream, start_pos) = if name == "." || name == ".." {
            self.alloc_sfn_entry()?
        } else {
            self.alloc_and_write_lfn_entries(&lfn_utf16, raw_entry.name())?
        };
        // write short name entry
        raw_entry.serialize(&mut stream)?;
        // Get position directory stream after entries were written
        let end_pos = stream.seek(io::SeekFrom::Current(0))?;
        // Get current absolute position on the storage
        // Unwrapping is safe because abs_pos() returns None only if stream is at position 0. This is not
        // the case because an entry was just written
        // Note: if current position is on the cluster boundary then a position in the cluster containing the entry is
        // returned
        let end_abs_pos = stream.abs_pos().unwrap();
        // Calculate SFN entry start position on the storage
        let start_abs_pos = end_abs_pos - u64::from(DIR_ENTRY_SIZE);
        // return new logical entry descriptor
        let short_name = ShortName::new(raw_entry.name());
        Ok(DirEntry {
            data: raw_entry,
            short_name,
            #[cfg(feature = "lfn")]
            lfn_utf16,
            fs: self.fs,
            entry_pos: start_abs_pos,
            offset_range: (start_pos, end_pos),
        })
    }
}

// Note: derive cannot be used because of invalid bounds. See: https://github.com/rust-lang/rust/issues/26925
impl<IO: ReadWriteSeek, TP: TimeProvider, OCC: OemCpConverter> Clone for Dir<'_, IO, TP, OCC> {
    fn clone(&self) -> Self {
        Self {
            stream: self.stream.clone(),
            fs: self.fs,
        }
    }
}

/// An iterator over the directory entries.
///
/// This struct is created by the `iter` method on `Dir`.
pub struct DirIter<'a, IO: ReadWriteSeek, TP, OCC> {
    stream: DirRawStream<'a, IO, TP, OCC>,
    fs: &'a FileSystem<IO, TP, OCC>,
    skip_volume: bool,
    err: bool,
}

impl<'a, IO: ReadWriteSeek, TP, OCC> DirIter<'a, IO, TP, OCC> {
    fn new(stream: DirRawStream<'a, IO, TP, OCC>, fs: &'a FileSystem<IO, TP, OCC>, skip_volume: bool) -> Self {
        DirIter {
            stream,
            fs,
            skip_volume,
            err: false,
        }
    }
}

impl<'a, IO: ReadWriteSeek, TP: TimeProvider, OCC> DirIter<'a, IO, TP, OCC> {
    fn should_skip_entry(&self, raw_entry: &DirEntryData) -> bool {
        if raw_entry.is_deleted() {
            return true;
        }
        match raw_entry {
            DirEntryData::File(sfn_entry) => self.skip_volume && sfn_entry.is_volume(),
            DirEntryData::Lfn(_) => false,
        }
    }

    #[allow(clippy::type_complexity)]
    fn read_dir_entry(&mut self) -> Result<Option<DirEntry<'a, IO, TP, OCC>>, Error<IO::Error>> {
        trace!("DirIter::read_dir_entry");
        let mut lfn_builder = LongNameBuilder::new();
        let mut offset = self.stream.seek(SeekFrom::Current(0))?;
        let mut begin_offset = offset;
        loop {
            let raw_entry = DirEntryData::deserialize(&mut self.stream)?;
            offset += u64::from(DIR_ENTRY_SIZE);
            // Check if this is end of dir
            if raw_entry.is_end() {
                return Ok(None);
            }
            // Check if this is deleted or volume ID entry
            if self.should_skip_entry(&raw_entry) {
                trace!("skip entry");
                lfn_builder.clear();
                begin_offset = offset;
                continue;
            }
            match raw_entry {
                DirEntryData::File(data) => {
                    // Get current absolute position on the storage
                    // Unwrapping is safe because abs_pos() returns None only if stream is at position 0. This is not
                    // the case because an entry was just read
                    // Note: if current position is on the cluster boundary then a position in the cluster containing the entry is
                    // returned
                    let end_abs_pos = self.stream.abs_pos().unwrap();
                    // Calculate SFN entry start position on the storage
                    let abs_pos = end_abs_pos - u64::from(DIR_ENTRY_SIZE);
                    // Check if LFN checksum is valid
                    lfn_builder.validate_chksum(data.name());
                    // Return directory entry
                    let short_name = ShortName::new(data.name());
                    trace!("file entry {:?}", data.name());
                    return Ok(Some(DirEntry {
                        data,
                        short_name,
                        #[cfg(feature = "lfn")]
                        lfn_utf16: lfn_builder.into_buf(),
                        fs: self.fs,
                        entry_pos: abs_pos,
                        offset_range: (begin_offset, offset),
                    }));
                }
                DirEntryData::Lfn(data) => {
                    // Append to LFN buffer
                    trace!("lfn entry");
                    lfn_builder.process(&data);
                }
            }
        }
    }
}

// Note: derive cannot be used because of invalid bounds. See: https://github.com/rust-lang/rust/issues/26925
impl<IO: ReadWriteSeek, TP, OCC> Clone for DirIter<'_, IO, TP, OCC> {
    fn clone(&self) -> Self {
        Self {
            stream: self.stream.clone(),
            fs: self.fs,
            err: self.err,
            skip_volume: self.skip_volume,
        }
    }
}

impl<'a, IO: ReadWriteSeek, TP: TimeProvider, OCC> Iterator for DirIter<'a, IO, TP, OCC> {
    type Item = Result<DirEntry<'a, IO, TP, OCC>, Error<IO::Error>>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.err {
            return None;
        }
        let r = self.read_dir_entry();
        match r {
            Ok(Some(e)) => Some(Ok(e)),
            Ok(None) => None,
            Err(err) => {
                self.err = true;
                Some(Err(err))
            }
        }
    }
}

#[rustfmt::skip]
fn validate_long_name<E: IoError>(name: &str) -> Result<(), Error<E>> {
    // check if length is valid
    if name.is_empty() {
        return Err(Error::InvalidFileNameLength);
    }
    if name.len() > MAX_LONG_NAME_LEN {
        return Err(Error::InvalidFileNameLength);
    }
    // check if there are only valid characters
    for c in name.chars() {
        match c {
            'a'..='z' | 'A'..='Z' | '0'..='9'
            | '\u{80}'..='\u{FFFF}'
            | '$' | '%' | '\'' | '-' | '_' | '@' | '~' | '`' | '!' | '(' | ')' | '{' | '}' | '.' | ' ' | '+' | ','
            | ';' | '=' | '[' | ']' | '^' | '#' | '&' => {},
            _ => return Err(Error::UnsupportedFileNameCharacter),
        }
    }
    Ok(())
}

fn lfn_checksum(short_name: &[u8; SFN_SIZE]) -> u8 {
    let mut chksum = num::Wrapping(0_u8);
    for b in short_name {
        chksum = (chksum << 7) + (chksum >> 1) + num::Wrapping(*b);
    }
    chksum.0
}

#[cfg(all(feature = "lfn", feature = "alloc"))]
#[derive(Clone)]
pub(crate) struct LfnBuffer {
    ucs2_units: Vec<u16>,
}

const MAX_LONG_NAME_LEN: usize = 255;

#[cfg(feature = "lfn")]
const MAX_LONG_DIR_ENTRIES: usize = (MAX_LONG_NAME_LEN + LFN_PART_LEN - 1) / LFN_PART_LEN;

#[cfg(all(feature = "lfn", not(feature = "alloc")))]
const LONG_NAME_BUFFER_LEN: usize = MAX_LONG_DIR_ENTRIES * LFN_PART_LEN;

#[cfg(all(feature = "lfn", not(feature = "alloc")))]
#[derive(Clone)]
pub(crate) struct LfnBuffer {
    ucs2_units: [u16; LONG_NAME_BUFFER_LEN],
    len: usize,
}

#[cfg(all(feature = "lfn", feature = "alloc"))]
impl LfnBuffer {
    fn new() -> Self {
        Self {
            ucs2_units: Vec::<u16>::new(),
        }
    }

    fn from_ucs2_units<I: Iterator<Item = u16>>(usc2_units: I) -> Self {
        Self {
            ucs2_units: usc2_units.collect(),
        }
    }

    fn clear(&mut self) {
        self.ucs2_units.clear();
    }

    pub(crate) fn len(&self) -> usize {
        self.ucs2_units.len()
    }

    fn set_len(&mut self, len: usize) {
        self.ucs2_units.resize(len, 0_u16);
    }

    pub(crate) fn as_ucs2_units(&self) -> &[u16] {
        &self.ucs2_units
    }
}

#[cfg(all(feature = "lfn", not(feature = "alloc")))]
impl LfnBuffer {
    fn new() -> Self {
        Self {
            ucs2_units: [0_u16; LONG_NAME_BUFFER_LEN],
            len: 0,
        }
    }

    fn from_ucs2_units<I: Iterator<Item = u16>>(usc2_units: I) -> Self {
        let mut lfn = Self {
            ucs2_units: [0_u16; LONG_NAME_BUFFER_LEN],
            len: 0,
        };
        for (i, usc2_unit) in usc2_units.enumerate() {
            lfn.ucs2_units[i] = usc2_unit;
            lfn.len += 1;
        }
        lfn
    }

    fn clear(&mut self) {
        self.ucs2_units = [0_u16; LONG_NAME_BUFFER_LEN];
        self.len = 0;
    }

    pub(crate) fn len(&self) -> usize {
        self.len
    }

    fn set_len(&mut self, len: usize) {
        self.len = len;
    }

    pub(crate) fn as_ucs2_units(&self) -> &[u16] {
        &self.ucs2_units[..self.len]
    }
}

#[cfg(not(feature = "lfn"))]
#[derive(Clone)]
pub(crate) struct LfnBuffer {}

#[cfg(not(feature = "lfn"))]
impl LfnBuffer {
    pub(crate) fn as_ucs2_units(&self) -> &[u16] {
        &[]
    }
}

#[cfg(feature = "lfn")]
struct LongNameBuilder {
    buf: LfnBuffer,
    chksum: u8,
    index: u8,
}

#[cfg(feature = "lfn")]
impl LongNameBuilder {
    fn new() -> Self {
        Self {
            buf: LfnBuffer::new(),
            chksum: 0,
            index: 0,
        }
    }

    fn clear(&mut self) {
        self.buf.clear();
        self.index = 0;
    }

    fn into_buf(mut self) -> LfnBuffer {
        // Check if last processed entry had index 1
        if self.index == 1 {
            self.truncate();
        } else if !self.is_empty() {
            warn!("unfinished LFN sequence {}", self.index);
            self.clear();
        }
        self.buf
    }

    fn truncate(&mut self) {
        // Truncate 0 and 0xFFFF characters from LFN buffer
        let ucs2_units = &self.buf.ucs2_units;
        let new_len = ucs2_units
            .iter()
            .rposition(|c| *c != 0xFFFF && *c != 0)
            .map_or(0, |n| n + 1);
        self.buf.set_len(new_len);
    }

    fn is_empty(&self) -> bool {
        // Check if any LFN entry has been processed
        // Note: index 0 is not a valid index in LFN and can be seen only after struct initialization
        self.index == 0
    }

    fn process(&mut self, data: &DirLfnEntryData) {
        let is_last = (data.order() & LFN_ENTRY_LAST_FLAG) != 0;
        let index = data.order() & 0x1F;
        if index == 0 || usize::from(index) > MAX_LONG_DIR_ENTRIES {
            // Corrupted entry
            warn!("currupted lfn entry! {:x}", data.order());
            self.clear();
            return;
        }
        if is_last {
            // last entry is actually first entry in stream
            self.index = index;
            self.chksum = data.checksum();
            self.buf.set_len(usize::from(index) * LFN_PART_LEN);
        } else if self.index == 0 || index != self.index - 1 || data.checksum() != self.chksum {
            // Corrupted entry
            warn!(
                "currupted lfn entry! {:x} {:x} {:x} {:x}",
                data.order(),
                self.index,
                data.checksum(),
                self.chksum
            );
            self.clear();
            return;
        } else {
            // Decrement LFN index only for non-last entries
            self.index -= 1;
        }
        let pos = LFN_PART_LEN * usize::from(index - 1);
        // copy name parts into LFN buffer
        data.copy_name_to_slice(&mut self.buf.ucs2_units[pos..pos + 13]);
    }

    fn validate_chksum(&mut self, short_name: &[u8; SFN_SIZE]) {
        if self.is_empty() {
            // Nothing to validate - no LFN entries has been processed
            return;
        }
        let chksum = lfn_checksum(short_name);
        if chksum != self.chksum {
            warn!("checksum mismatch {:x} {:x} {:?}", chksum, self.chksum, short_name);
            self.clear();
        }
    }
}

// Dummy implementation for non-alloc build
#[cfg(not(feature = "lfn"))]
struct LongNameBuilder {}
#[cfg(not(feature = "lfn"))]
impl LongNameBuilder {
    fn new() -> Self {
        LongNameBuilder {}
    }
    fn clear(&mut self) {}
    fn into_vec(self) {}
    fn truncate(&mut self) {}
    fn process(&mut self, _data: &DirLfnEntryData) {}
    fn validate_chksum(&mut self, _short_name: &[u8; SFN_SIZE]) {}
}

#[cfg(feature = "lfn")]
struct LfnEntriesGenerator<'a> {
    name_parts_iter: iter::Rev<slice::Chunks<'a, u16>>,
    checksum: u8,
    index: usize,
    num: usize,
    ended: bool,
}

#[cfg(feature = "lfn")]
impl<'a> LfnEntriesGenerator<'a> {
    fn new(name_utf16: &'a [u16], checksum: u8) -> Self {
        let num_entries = (name_utf16.len() + LFN_PART_LEN - 1) / LFN_PART_LEN;
        // create generator using reverse iterator over chunks - first chunk can be shorter
        LfnEntriesGenerator {
            checksum,
            name_parts_iter: name_utf16.chunks(LFN_PART_LEN).rev(),
            index: 0,
            num: num_entries,
            ended: false,
        }
    }
}

#[cfg(feature = "lfn")]
impl Iterator for LfnEntriesGenerator<'_> {
    type Item = DirLfnEntryData;

    fn next(&mut self) -> Option<Self::Item> {
        if self.ended {
            return None;
        }

        // get next part from reverse iterator
        if let Some(name_part) = self.name_parts_iter.next() {
            let lfn_index = self.num - self.index;
            let mut order = lfn_index as u8;
            if self.index == 0 {
                // this is last name part (written as first)
                order |= LFN_ENTRY_LAST_FLAG;
            }
            debug_assert!(order > 0);
            let mut lfn_part = [LFN_PADDING; LFN_PART_LEN];
            lfn_part[..name_part.len()].copy_from_slice(name_part);
            if name_part.len() < LFN_PART_LEN {
                // name is only zero-terminated if its length is not multiplicity of LFN_PART_LEN
                lfn_part[name_part.len()] = 0;
            }
            // create and return new LFN entry
            let mut lfn_entry = DirLfnEntryData::new(order, self.checksum);
            lfn_entry.copy_name_from_slice(&lfn_part);
            self.index += 1;
            Some(lfn_entry)
        } else {
            // end of name
            self.ended = true;
            None
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.name_parts_iter.size_hint()
    }
}

// name_parts_iter is ExactSizeIterator so size_hint returns one limit
#[cfg(feature = "lfn")]
impl ExactSizeIterator for LfnEntriesGenerator<'_> {}

// Dummy implementation for non-alloc build
#[cfg(not(feature = "lfn"))]
struct LfnEntriesGenerator {}
#[cfg(not(feature = "lfn"))]
impl LfnEntriesGenerator {
    fn new(_name_utf16: &[u16], _checksum: u8) -> Self {
        LfnEntriesGenerator {}
    }
}
#[cfg(not(feature = "lfn"))]
impl Iterator for LfnEntriesGenerator {
    type Item = DirLfnEntryData;

    fn next(&mut self) -> Option<Self::Item> {
        None
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (0, Some(0))
    }
}
#[cfg(not(feature = "lfn"))]
impl ExactSizeIterator for LfnEntriesGenerator {}

#[derive(Default, Debug, Clone)]
struct ShortNameGenerator {
    chksum: u16,
    long_prefix_bitmap: u16,
    prefix_chksum_bitmap: u16,
    name_fits: bool,
    lossy_conv: bool,
    exact_match: bool,
    basename_len: usize,
    short_name: [u8; SFN_SIZE],
}

impl ShortNameGenerator {
    fn new(name: &str) -> Self {
        // padded by ' '
        let mut short_name = [SFN_PADDING; SFN_SIZE];
        // find extension after last dot
        // Note: short file name cannot start with the extension
        let dot_index_opt = name[1..].rfind('.').map(|index| index + 1);
        // copy basename (part of filename before a dot)
        let basename_src = dot_index_opt.map_or(name, |dot_index| &name[..dot_index]);
        let (basename_len, basename_fits, basename_lossy) =
            Self::copy_short_name_part(&mut short_name[0..8], basename_src);
        // copy file extension if exists
        let (name_fits, lossy_conv) = dot_index_opt.map_or((basename_fits, basename_lossy), |dot_index| {
            let (_, ext_fits, ext_lossy) = Self::copy_short_name_part(&mut short_name[8..11], &name[dot_index + 1..]);
            (basename_fits && ext_fits, basename_lossy || ext_lossy)
        });
        let chksum = Self::checksum(name);
        Self {
            chksum,
            name_fits,
            lossy_conv,
            basename_len,
            short_name,
            ..Self::default()
        }
    }

    fn generate_dot() -> [u8; SFN_SIZE] {
        let mut short_name = [SFN_PADDING; SFN_SIZE];
        short_name[0] = b'.';
        short_name
    }

    fn generate_dotdot() -> [u8; SFN_SIZE] {
        let mut short_name = [SFN_PADDING; SFN_SIZE];
        short_name[0] = b'.';
        short_name[1] = b'.';
        short_name
    }

    fn copy_short_name_part(dst: &mut [u8], src: &str) -> (usize, bool, bool) {
        let mut dst_pos = 0;
        let mut lossy_conv = false;
        for c in src.chars() {
            if dst_pos == dst.len() {
                // result buffer is full
                return (dst_pos, false, lossy_conv);
            }
            // Make sure character is allowed in 8.3 name
            #[rustfmt::skip]
            let fixed_c = match c {
                // strip spaces and dots
                ' ' | '.' => {
                    lossy_conv = true;
                    continue;
                },
                // copy allowed characters
                'A'..='Z' | 'a'..='z' | '0'..='9'
                | '!' | '#' | '$' | '%' | '&' | '\'' | '(' | ')' | '-' | '@' | '^' | '_' | '`' | '{' | '}' | '~' => c,
                // replace disallowed characters by underscore
                _ => '_',
            };
            // Update 'lossy conversion' flag
            lossy_conv = lossy_conv || (fixed_c != c);
            // short name is always uppercase
            let upper = fixed_c.to_ascii_uppercase();
            dst[dst_pos] = upper as u8; // SAFE: upper is in range 0x20-0x7F
            dst_pos += 1;
        }
        (dst_pos, true, lossy_conv)
    }

    fn add_existing(&mut self, short_name: &[u8; SFN_SIZE]) {
        // check for exact match collision
        if short_name == &self.short_name {
            self.exact_match = true;
        }
        // check for long prefix form collision (TEXTFI~1.TXT)
        self.check_for_long_prefix_collision(short_name);

        // check for short prefix + checksum form collision (TE021F~1.TXT)
        self.check_for_short_prefix_collision(short_name);
    }

    fn check_for_long_prefix_collision(&mut self, short_name: &[u8; SFN_SIZE]) {
        // check for long prefix form collision (TEXTFI~1.TXT)
        let long_prefix_len = 6.min(self.basename_len);
        if short_name[long_prefix_len] != b'~' {
            return;
        }
        if let Some(num_suffix) = char::from(short_name[long_prefix_len + 1]).to_digit(10) {
            let long_prefix_matches = short_name[..long_prefix_len] == self.short_name[..long_prefix_len];
            let ext_matches = short_name[8..] == self.short_name[8..];
            if long_prefix_matches && ext_matches {
                self.long_prefix_bitmap |= 1 << num_suffix;
            }
        }
    }

    fn check_for_short_prefix_collision(&mut self, short_name: &[u8; SFN_SIZE]) {
        // check for short prefix + checksum form collision (TE021F~1.TXT)
        let short_prefix_len = 2.min(self.basename_len);
        if short_name[short_prefix_len + 4] != b'~' {
            return;
        }
        if let Some(num_suffix) = char::from(short_name[short_prefix_len + 4 + 1]).to_digit(10) {
            let short_prefix_matches = short_name[..short_prefix_len] == self.short_name[..short_prefix_len];
            let ext_matches = short_name[8..] == self.short_name[8..];
            if short_prefix_matches && ext_matches {
                let chksum_res = str::from_utf8(&short_name[short_prefix_len..short_prefix_len + 4])
                    .map(|s| u16::from_str_radix(s, 16));
                if chksum_res == Ok(Ok(self.chksum)) {
                    self.prefix_chksum_bitmap |= 1 << num_suffix;
                }
            }
        }
    }

    fn checksum(name: &str) -> u16 {
        // BSD checksum algorithm
        let mut chksum = num::Wrapping(0_u16);
        for c in name.chars() {
            chksum = (chksum >> 1) + (chksum << 15) + num::Wrapping(c as u16);
        }
        chksum.0
    }

    fn generate(&self) -> Result<[u8; SFN_SIZE], Error<()>> {
        if !self.lossy_conv && self.name_fits && !self.exact_match {
            // If there was no lossy conversion and name fits into
            // 8.3 convention and there is no collision return it as is
            return Ok(self.short_name);
        }
        // Try using long 6-characters prefix
        for i in 1..5 {
            if self.long_prefix_bitmap & (1 << i) == 0 {
                return Ok(self.build_prefixed_name(i, false));
            }
        }
        // Try prefix with checksum
        for i in 1..10 {
            if self.prefix_chksum_bitmap & (1 << i) == 0 {
                return Ok(self.build_prefixed_name(i, true));
            }
        }
        // Too many collisions - fail
        Err(Error::AlreadyExists)
    }

    fn next_iteration(&mut self) {
        // Try different checksum in next iteration
        self.chksum = (num::Wrapping(self.chksum) + num::Wrapping(1)).0;
        // Zero bitmaps
        self.long_prefix_bitmap = 0;
        self.prefix_chksum_bitmap = 0;
    }

    fn build_prefixed_name(&self, num: u32, with_chksum: bool) -> [u8; SFN_SIZE] {
        let mut buf = [SFN_PADDING; SFN_SIZE];
        let prefix_len = if with_chksum {
            let prefix_len = 2.min(self.basename_len);
            buf[..prefix_len].copy_from_slice(&self.short_name[..prefix_len]);
            buf[prefix_len..prefix_len + 4].copy_from_slice(&Self::u16_to_hex(self.chksum));
            prefix_len + 4
        } else {
            let prefix_len = 6.min(self.basename_len);
            buf[..prefix_len].copy_from_slice(&self.short_name[..prefix_len]);
            prefix_len
        };
        buf[prefix_len] = b'~';
        buf[prefix_len + 1] = char::from_digit(num, 10).unwrap() as u8; // SAFE: num is in range [1, 9]
        buf[8..].copy_from_slice(&self.short_name[8..]);
        buf
    }

    fn u16_to_hex(x: u16) -> [u8; 4] {
        // Unwrapping below is safe because each line takes 4 bits of `x` and shifts them to the right so they form
        // a number in range [0, 15]
        let x_u32 = u32::from(x);
        let mut hex_bytes = [
            char::from_digit((x_u32 >> 12) & 0xF, 16).unwrap() as u8,
            char::from_digit((x_u32 >> 8) & 0xF, 16).unwrap() as u8,
            char::from_digit((x_u32 >> 4) & 0xF, 16).unwrap() as u8,
            char::from_digit(x_u32 & 0xF, 16).unwrap() as u8,
        ];
        hex_bytes.make_ascii_uppercase();
        hex_bytes
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_split_path() {
        assert_eq!(split_path("aaa/bbb/ccc"), ("aaa", Some("bbb/ccc")));
        assert_eq!(split_path("aaa/bbb"), ("aaa", Some("bbb")));
        assert_eq!(split_path("aaa"), ("aaa", None));
    }

    #[test]
    fn test_generate_short_name() {
        assert_eq!(ShortNameGenerator::new("Foo").generate().ok(), Some(*b"FOO        "));
        assert_eq!(ShortNameGenerator::new("Foo.b").generate().ok(), Some(*b"FOO     B  "));
        assert_eq!(
            ShortNameGenerator::new("Foo.baR").generate().ok(),
            Some(*b"FOO     BAR")
        );
        assert_eq!(
            ShortNameGenerator::new("Foo+1.baR").generate().ok(),
            Some(*b"FOO_1~1 BAR")
        );
        assert_eq!(
            ShortNameGenerator::new("ver +1.2.text").generate().ok(),
            Some(*b"VER_12~1TEX")
        );
        assert_eq!(
            ShortNameGenerator::new(".bashrc.swp").generate().ok(),
            Some(*b"BASHRC~1SWP")
        );
        assert_eq!(ShortNameGenerator::new(".foo").generate().ok(), Some(*b"FOO~1      "));
    }

    #[test]
    fn test_short_name_checksum_overflow() {
        ShortNameGenerator::checksum("\u{FF5A}\u{FF5A}\u{FF5A}\u{FF5A}");
    }

    #[test]
    fn test_lfn_checksum_overflow() {
        lfn_checksum(&[0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF]);
    }

    #[test]
    fn test_generate_short_name_collisions_long() {
        let mut buf: [u8; SFN_SIZE];
        let mut gen = ShortNameGenerator::new("TextFile.Mine.txt");
        buf = gen.generate().unwrap();
        assert_eq!(&buf, b"TEXTFI~1TXT");
        gen.add_existing(&buf);
        buf = gen.generate().unwrap();
        assert_eq!(&buf, b"TEXTFI~2TXT");
        gen.add_existing(&buf);
        buf = gen.generate().unwrap();
        assert_eq!(&buf, b"TEXTFI~3TXT");
        gen.add_existing(&buf);
        buf = gen.generate().unwrap();
        assert_eq!(&buf, b"TEXTFI~4TXT");
        gen.add_existing(&buf);
        buf = gen.generate().unwrap();
        assert_eq!(&buf, b"TE527D~1TXT");
        gen.add_existing(&buf);
        buf = gen.generate().unwrap();
        assert_eq!(&buf, b"TE527D~2TXT");
        for i in 3..10 {
            gen.add_existing(&buf);
            buf = gen.generate().unwrap();
            assert_eq!(&buf, format!("TE527D~{}TXT", i).as_bytes());
        }
        gen.add_existing(&buf);
        assert!(gen.generate().is_err());
        gen.next_iteration();
        for _i in 0..4 {
            buf = gen.generate().unwrap();
            gen.add_existing(&buf);
        }
        buf = gen.generate().unwrap();
        assert_eq!(&buf, b"TE527E~1TXT");
    }

    #[test]
    fn test_generate_short_name_collisions_short() {
        let mut buf: [u8; SFN_SIZE];
        let mut gen = ShortNameGenerator::new("x.txt");
        buf = gen.generate().unwrap();
        assert_eq!(&buf, b"X       TXT");
        gen.add_existing(&buf);
        buf = gen.generate().unwrap();
        assert_eq!(&buf, b"X~1     TXT");
        gen.add_existing(&buf);
        buf = gen.generate().unwrap();
        assert_eq!(&buf, b"X~2     TXT");
        gen.add_existing(&buf);
        buf = gen.generate().unwrap();
        assert_eq!(&buf, b"X~3     TXT");
        gen.add_existing(&buf);
        buf = gen.generate().unwrap();
        assert_eq!(&buf, b"X~4     TXT");
        gen.add_existing(&buf);
        buf = gen.generate().unwrap();
        assert_eq!(&buf, b"X40DA~1 TXT");
        gen.add_existing(&buf);
        buf = gen.generate().unwrap();
        assert_eq!(&buf, b"X40DA~2 TXT");
    }
}
