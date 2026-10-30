#[cfg(all(not(feature = "std"), feature = "alloc"))]
use alloc::string::String;
use bitflags::bitflags;
use core::char;
use core::convert::TryInto;
use core::fmt;
#[cfg(not(feature = "unicode"))]
use core::iter;

#[cfg(feature = "lfn")]
use crate::dir::LfnBuffer;
use crate::dir::{Dir, DirRawStream};
use crate::error::{Error, IoError};
use crate::file::File;
use crate::fs::{FatType, FileSystem, OemCpConverter, ReadWriteSeek};
use crate::io::{self, Read, ReadLeExt, Write, WriteLeExt};
use crate::time::{Date, DateTime};

bitflags! {
    /// A FAT file attributes.
    #[derive(Default, Debug, Clone, Copy, PartialEq, Eq)]
    pub struct FileAttributes: u8 {
        const READ_ONLY  = 0x01;
        const HIDDEN     = 0x02;
        const SYSTEM     = 0x04;
        const VOLUME_ID  = 0x08;
        const DIRECTORY  = 0x10;
        const ARCHIVE    = 0x20;
        const LFN        = Self::READ_ONLY.bits() | Self::HIDDEN.bits()
                         | Self::SYSTEM.bits() | Self::VOLUME_ID.bits();
    }
}

// Size of single directory entry in bytes
pub(crate) const DIR_ENTRY_SIZE: u32 = 32;

// Directory entry flags available in first byte of the short name
pub(crate) const DIR_ENTRY_DELETED_FLAG: u8 = 0xE5;
pub(crate) const DIR_ENTRY_REALLY_E5_FLAG: u8 = 0x05;

// Short file name field size in bytes (besically 8 + 3)
pub(crate) const SFN_SIZE: usize = 11;

// Byte used for short name padding
pub(crate) const SFN_PADDING: u8 = b' ';

// Length in characters of a LFN fragment packed in one directory entry
pub(crate) const LFN_PART_LEN: usize = 13;

// Bit used in order field to mark last LFN entry
#[cfg(feature = "lfn")]
pub(crate) const LFN_ENTRY_LAST_FLAG: u8 = 0x40;

// Character to upper case conversion which supports Unicode only if `unicode` feature is enabled
#[cfg(feature = "unicode")]
fn char_to_uppercase(c: char) -> char::ToUppercase {
    c.to_uppercase()
}
#[cfg(not(feature = "unicode"))]
fn char_to_uppercase(c: char) -> iter::Once<char> {
    iter::once(c.to_ascii_uppercase())
}

/// Decoded file short name
#[derive(Clone, Debug, Default)]
pub(crate) struct ShortName {
    name: [u8; 12],
    len: u8,
}

impl ShortName {
    pub(crate) fn new(raw_name: &[u8; SFN_SIZE]) -> Self {
        // get name components length by looking for space character
        let name_len = raw_name[0..8]
            .iter()
            .rposition(|x| *x != SFN_PADDING)
            .map_or(0, |p| p + 1);
        let ext_len = raw_name[8..11]
            .iter()
            .rposition(|x| *x != SFN_PADDING)
            .map_or(0, |p| p + 1);
        let mut name = [SFN_PADDING; 12];
        name[..name_len].copy_from_slice(&raw_name[..name_len]);
        let total_len = if ext_len > 0 {
            name[name_len] = b'.';
            name[name_len + 1..name_len + 1 + ext_len].copy_from_slice(&raw_name[8..8 + ext_len]);
            // Return total name length
            name_len + 1 + ext_len
        } else {
            // No extension - return length of name part
            name_len
        };
        // FAT encodes character 0xE5 as 0x05 because 0xE5 marks deleted files
        if name[0] == DIR_ENTRY_REALLY_E5_FLAG {
            name[0] = 0xE5;
        }
        // Short names in FAT filesystem are encoded in OEM code-page
        Self {
            name,
            len: total_len as u8,
        }
    }

    fn as_bytes(&self) -> &[u8] {
        &self.name[..usize::from(self.len)]
    }

    #[cfg(feature = "alloc")]
    fn to_string<OCC: OemCpConverter>(&self, oem_cp_converter: &OCC) -> String {
        // Strip non-ascii characters from short name
        self.as_bytes()
            .iter()
            .copied()
            .map(|c| oem_cp_converter.decode(c))
            .collect()
    }

    fn eq_ignore_case<OCC: OemCpConverter>(&self, name: &str, oem_cp_converter: &OCC) -> bool {
        // Convert name to UTF-8 character iterator
        let byte_iter = self.as_bytes().iter().copied();
        let char_iter = byte_iter.map(|c| oem_cp_converter.decode(c));
        // Compare interators ignoring case
        let uppercase_char_iter = char_iter.flat_map(char_to_uppercase);
        uppercase_char_iter.eq(name.chars().flat_map(char_to_uppercase))
    }
}

#[allow(dead_code)]
#[derive(Clone, Debug, Default)]
pub(crate) struct DirFileEntryData {
    name: [u8; SFN_SIZE],
    attrs: FileAttributes,
    reserved_0: u8,
    create_time_0: u8,
    create_time_1: u16,
    create_date: u16,
    access_date: u16,
    first_cluster_hi: u16,
    modify_time: u16,
    modify_date: u16,
    first_cluster_lo: u16,
    size: u32,
}

impl DirFileEntryData {
    pub(crate) fn new(name: [u8; SFN_SIZE], attrs: FileAttributes) -> Self {
        Self {
            name,
            attrs,
            ..Self::default()
        }
    }

    pub(crate) fn renamed(&self, new_name: [u8; SFN_SIZE]) -> Self {
        let mut sfn_entry = self.clone();
        sfn_entry.name = new_name;
        sfn_entry
    }

    pub(crate) fn name(&self) -> &[u8; SFN_SIZE] {
        &self.name
    }

    #[cfg(feature = "alloc")]
    fn lowercase_name(&self) -> ShortName {
        let mut name_copy: [u8; SFN_SIZE] = self.name;
        if self.lowercase_basename() {
            name_copy[..8].make_ascii_lowercase();
        }
        if self.lowercase_ext() {
            name_copy[8..].make_ascii_lowercase();
        }
        ShortName::new(&name_copy)
    }

    pub(crate) fn first_cluster(&self, fat_type: FatType) -> Option<u32> {
        let first_cluster_hi = if fat_type == FatType::Fat32 {
            self.first_cluster_hi
        } else {
            0
        };
        let n = (u32::from(first_cluster_hi) << 16) | u32::from(self.first_cluster_lo);
        if n == 0 {
            None
        } else {
            Some(n)
        }
    }

    pub(crate) fn set_first_cluster(&mut self, cluster: Option<u32>, fat_type: FatType) {
        let n = cluster.unwrap_or(0);
        if fat_type == FatType::Fat32 {
            self.first_cluster_hi = (n >> 16) as u16;
        }
        self.first_cluster_lo = (n & 0xFFFF) as u16;
    }

    pub(crate) fn size(&self) -> Option<u32> {
        if self.is_file() {
            Some(self.size)
        } else {
            None
        }
    }

    fn set_size(&mut self, size: u32) {
        self.size = size;
    }

    pub(crate) fn is_dir(&self) -> bool {
        self.attrs.contains(FileAttributes::DIRECTORY)
    }

    fn is_file(&self) -> bool {
        !self.is_dir()
    }

    fn lowercase_basename(&self) -> bool {
        self.reserved_0 & (1 << 3) != 0
    }

    fn lowercase_ext(&self) -> bool {
        self.reserved_0 & (1 << 4) != 0
    }

    fn created(&self) -> DateTime {
        DateTime::decode(self.create_date, self.create_time_1, self.create_time_0)
    }

    fn accessed(&self) -> Date {
        Date::decode(self.access_date)
    }

    fn modified(&self) -> DateTime {
        DateTime::decode(self.modify_date, self.modify_time, 0)
    }

    pub(crate) fn set_created(&mut self, date_time: DateTime) {
        self.create_date = date_time.date.encode();
        let encoded_time = date_time.time.encode();
        self.create_time_1 = encoded_time.0;
        self.create_time_0 = encoded_time.1;
    }

    pub(crate) fn set_accessed(&mut self, date: Date) {
        self.access_date = date.encode();
    }

    pub(crate) fn set_modified(&mut self, date_time: DateTime) {
        self.modify_date = date_time.date.encode();
        self.modify_time = date_time.time.encode().0;
    }

    pub(crate) fn serialize<W: Write>(&self, wrt: &mut W) -> Result<(), W::Error> {
        wrt.write_all(&self.name)?;
        wrt.write_u8(self.attrs.bits())?;
        wrt.write_u8(self.reserved_0)?;
        wrt.write_u8(self.create_time_0)?;
        wrt.write_u16_le(self.create_time_1)?;
        wrt.write_u16_le(self.create_date)?;
        wrt.write_u16_le(self.access_date)?;
        wrt.write_u16_le(self.first_cluster_hi)?;
        wrt.write_u16_le(self.modify_time)?;
        wrt.write_u16_le(self.modify_date)?;
        wrt.write_u16_le(self.first_cluster_lo)?;
        wrt.write_u32_le(self.size)?;
        Ok(())
    }

    pub(crate) fn is_deleted(&self) -> bool {
        self.name[0] == DIR_ENTRY_DELETED_FLAG
    }

    pub(crate) fn set_deleted(&mut self) {
        self.name[0] = DIR_ENTRY_DELETED_FLAG;
    }

    pub(crate) fn is_end(&self) -> bool {
        self.name[0] == 0
    }

    pub(crate) fn is_volume(&self) -> bool {
        self.attrs.contains(FileAttributes::VOLUME_ID)
    }
}

#[allow(dead_code)]
#[derive(Clone, Debug, Default)]
pub(crate) struct DirLfnEntryData {
    order: u8,
    name_0: [u16; 5],
    attrs: FileAttributes,
    entry_type: u8,
    checksum: u8,
    name_1: [u16; 6],
    reserved_0: u16,
    name_2: [u16; 2],
}

impl DirLfnEntryData {
    pub(crate) fn new(order: u8, checksum: u8) -> Self {
        Self {
            order,
            checksum,
            attrs: FileAttributes::LFN,
            ..Self::default()
        }
    }

    pub(crate) fn copy_name_from_slice(&mut self, lfn_part: &[u16; LFN_PART_LEN]) {
        self.name_0.copy_from_slice(&lfn_part[0..5]);
        self.name_1.copy_from_slice(&lfn_part[5..5 + 6]);
        self.name_2.copy_from_slice(&lfn_part[11..11 + 2]);
    }

    pub(crate) fn copy_name_to_slice(&self, lfn_part: &mut [u16]) {
        debug_assert!(lfn_part.len() == LFN_PART_LEN);
        lfn_part[0..5].copy_from_slice(&self.name_0);
        lfn_part[5..11].copy_from_slice(&self.name_1);
        lfn_part[11..13].copy_from_slice(&self.name_2);
    }

    pub(crate) fn serialize<W: Write>(&self, wrt: &mut W) -> Result<(), W::Error> {
        wrt.write_u8(self.order)?;
        for ch in &self.name_0 {
            wrt.write_u16_le(*ch)?;
        }
        wrt.write_u8(self.attrs.bits())?;
        wrt.write_u8(self.entry_type)?;
        wrt.write_u8(self.checksum)?;
        for ch in &self.name_1 {
            wrt.write_u16_le(*ch)?;
        }
        wrt.write_u16_le(self.reserved_0)?;
        for ch in &self.name_2 {
            wrt.write_u16_le(*ch)?;
        }
        Ok(())
    }

    pub(crate) fn order(&self) -> u8 {
        self.order
    }

    pub(crate) fn checksum(&self) -> u8 {
        self.checksum
    }

    pub(crate) fn is_deleted(&self) -> bool {
        self.order == DIR_ENTRY_DELETED_FLAG
    }

    pub(crate) fn set_deleted(&mut self) {
        self.order = DIR_ENTRY_DELETED_FLAG;
    }

    pub(crate) fn is_end(&self) -> bool {
        self.order == 0
    }
}

#[derive(Clone, Debug)]
pub(crate) enum DirEntryData {
    File(DirFileEntryData),
    Lfn(DirLfnEntryData),
}

impl DirEntryData {
    pub(crate) fn serialize<E: IoError, W: Write<Error = Error<E>>>(&self, wrt: &mut W) -> Result<(), Error<E>> {
        trace!("DirEntryData::serialize");
        match self {
            DirEntryData::File(file) => file.serialize(wrt),
            DirEntryData::Lfn(lfn) => lfn.serialize(wrt),
        }
    }

    pub(crate) fn deserialize<E: IoError, R: Read<Error = Error<E>>>(rdr: &mut R) -> Result<Self, Error<E>> {
        trace!("DirEntryData::deserialize");
        let mut name = [0; SFN_SIZE];
        match rdr.read_exact(&mut name) {
            Err(Error::UnexpectedEof) => {
                // entries can occupy all clusters of directory so there is no zero entry at the end
                // handle it here by returning non-existing empty entry
                return Ok(DirEntryData::File(DirFileEntryData::default()));
            }
            Err(err) => {
                return Err(err);
            }
            Ok(()) => {}
        }
        let attrs = FileAttributes::from_bits_truncate(rdr.read_u8()?);
        if attrs & FileAttributes::LFN == FileAttributes::LFN {
            // read long name entry
            let mut data = DirLfnEntryData {
                attrs,
                ..DirLfnEntryData::default()
            };
            // divide the name into order and LFN name_0
            data.order = name[0];
            for (dst, src) in data.name_0.iter_mut().zip(name[1..].chunks_exact(2)) {
                // unwrap cannot panic because src has exactly 2 values
                *dst = u16::from_le_bytes(src.try_into().unwrap());
            }

            data.entry_type = rdr.read_u8()?;
            data.checksum = rdr.read_u8()?;
            for x in &mut data.name_1 {
                *x = rdr.read_u16_le()?;
            }
            data.reserved_0 = rdr.read_u16_le()?;
            for x in &mut data.name_2 {
                *x = rdr.read_u16_le()?;
            }
            Ok(DirEntryData::Lfn(data))
        } else {
            // read short name entry
            let data = DirFileEntryData {
                name,
                attrs,
                reserved_0: rdr.read_u8()?,
                create_time_0: rdr.read_u8()?,
                create_time_1: rdr.read_u16_le()?,
                create_date: rdr.read_u16_le()?,
                access_date: rdr.read_u16_le()?,
                first_cluster_hi: rdr.read_u16_le()?,
                modify_time: rdr.read_u16_le()?,
                modify_date: rdr.read_u16_le()?,
                first_cluster_lo: rdr.read_u16_le()?,
                size: rdr.read_u32_le()?,
            };
            Ok(DirEntryData::File(data))
        }
    }

    pub(crate) fn is_deleted(&self) -> bool {
        match self {
            DirEntryData::File(file) => file.is_deleted(),
            DirEntryData::Lfn(lfn) => lfn.is_deleted(),
        }
    }

    pub(crate) fn set_deleted(&mut self) {
        match self {
            DirEntryData::File(file) => file.set_deleted(),
            DirEntryData::Lfn(lfn) => lfn.set_deleted(),
        }
    }

    pub(crate) fn is_end(&self) -> bool {
        match self {
            DirEntryData::File(file) => file.is_end(),
            DirEntryData::Lfn(lfn) => lfn.is_end(),
        }
    }
}

#[derive(Clone, Debug)]
pub(crate) struct DirEntryEditor {
    data: DirFileEntryData,
    pos: u64,
    dirty: bool,
}

impl DirEntryEditor {
    fn new(data: DirFileEntryData, pos: u64) -> Self {
        Self {
            data,
            pos,
            dirty: false,
        }
    }

    pub(crate) fn inner(&self) -> &DirFileEntryData {
        &self.data
    }

    pub(crate) fn set_first_cluster(&mut self, first_cluster: Option<u32>, fat_type: FatType) {
        if first_cluster != self.data.first_cluster(fat_type) {
            self.data.set_first_cluster(first_cluster, fat_type);
            self.dirty = true;
        }
    }

    pub(crate) fn set_size(&mut self, size: u32) {
        match self.data.size() {
            Some(n) if size != n => {
                self.data.set_size(size);
                self.dirty = true;
            }
            _ => {}
        }
    }

    pub(crate) fn set_created(&mut self, date_time: DateTime) {
        if date_time != self.data.created() {
            self.data.set_created(date_time);
            self.dirty = true;
        }
    }

    pub(crate) fn set_accessed(&mut self, date: Date) {
        if date != self.data.accessed() {
            self.data.set_accessed(date);
            self.dirty = true;
        }
    }

    pub(crate) fn set_modified(&mut self, date_time: DateTime) {
        if date_time != self.data.modified() {
            self.data.set_modified(date_time);
            self.dirty = true;
        }
    }

    pub(crate) fn flush<IO: ReadWriteSeek, TP, OCC>(&mut self, fs: &FileSystem<IO, TP, OCC>) -> Result<(), IO::Error> {
        if self.dirty {
            self.write(fs)?;
            self.dirty = false;
        }
        Ok(())
    }

    fn write<IO: ReadWriteSeek, TP, OCC>(&self, fs: &FileSystem<IO, TP, OCC>) -> Result<(), IO::Error> {
        let mut disk = fs.disk.borrow_mut();
        disk.seek(io::SeekFrom::Start(self.pos))?;
        self.data.serialize(&mut *disk)
    }
}

/// A FAT directory entry.
///
/// `DirEntry` is returned by `DirIter` when reading a directory.
#[derive(Clone)]
pub struct DirEntry<'a, IO: ReadWriteSeek, TP, OCC> {
    pub(crate) data: DirFileEntryData,
    pub(crate) short_name: ShortName,
    #[cfg(feature = "lfn")]
    pub(crate) lfn_utf16: LfnBuffer,
    pub(crate) entry_pos: u64,
    pub(crate) offset_range: (u64, u64),
    pub(crate) fs: &'a FileSystem<IO, TP, OCC>,
}

#[allow(clippy::len_without_is_empty)]
impl<'a, IO: ReadWriteSeek, TP, OCC: OemCpConverter> DirEntry<'a, IO, TP, OCC> {
    /// Returns short file name.
    ///
    /// Non-ASCII characters are replaced by the replacement character (U+FFFD).
    #[cfg(feature = "alloc")]
    #[must_use]
    pub fn short_file_name(&self) -> String {
        self.short_name.to_string(&self.fs.options.oem_cp_converter)
    }

    /// Returns short file name as byte array slice.
    ///
    /// Characters are encoded in the OEM codepage.
    #[must_use]
    pub fn short_file_name_as_bytes(&self) -> &[u8] {
        self.short_name.as_bytes()
    }

    /// Returns long file name as u16 array slice.
    ///
    /// Characters are encoded in the UCS-2 encoding.
    #[cfg(feature = "lfn")]
    #[must_use]
    pub fn long_file_name_as_ucs2_units(&self) -> Option<&[u16]> {
        if self.lfn_utf16.len() > 0 {
            Some(self.lfn_utf16.as_ucs2_units())
        } else {
            None
        }
    }

    /// Returns long file name or if it doesn't exist fallbacks to short file name.
    #[cfg(feature = "alloc")]
    #[must_use]
    pub fn file_name(&self) -> String {
        #[cfg(feature = "lfn")]
        {
            let lfn_opt = self.long_file_name_as_ucs2_units();
            if let Some(lfn) = lfn_opt {
                return String::from_utf16_lossy(lfn);
            }
        }

        self.data.lowercase_name().to_string(&self.fs.options.oem_cp_converter)
    }

    /// Returns file attributes.
    #[must_use]
    pub fn attributes(&self) -> FileAttributes {
        self.data.attrs
    }

    /// Checks if entry belongs to directory.
    #[must_use]
    pub fn is_dir(&self) -> bool {
        self.data.is_dir()
    }

    /// Checks if entry belongs to regular file.
    #[must_use]
    pub fn is_file(&self) -> bool {
        self.data.is_file()
    }

    pub(crate) fn first_cluster(&self) -> Option<u32> {
        self.data.first_cluster(self.fs.fat_type())
    }

    fn editor(&self) -> DirEntryEditor {
        DirEntryEditor::new(self.data.clone(), self.entry_pos)
    }

    pub(crate) fn is_same_entry(&self, other: &DirEntry<IO, TP, OCC>) -> bool {
        self.entry_pos == other.entry_pos
    }

    /// Returns `File` struct for this entry.
    ///
    /// # Panics
    ///
    /// Will panic if this is not a file.
    #[must_use]
    pub fn to_file(&self) -> File<'a, IO, TP, OCC> {
        assert!(!self.is_dir(), "Not a file entry");
        File::new(self.first_cluster(), Some(self.editor()), self.fs)
    }

    /// Returns `Dir` struct for this entry.
    ///
    /// # Panics
    ///
    /// Will panic if this is not a directory.
    #[must_use]
    pub fn to_dir(&self) -> Dir<'a, IO, TP, OCC> {
        assert!(self.is_dir(), "Not a directory entry");
        match self.first_cluster() {
            Some(n) => {
                let file = File::new(Some(n), Some(self.editor()), self.fs);
                Dir::new(DirRawStream::File(file), self.fs)
            }
            None => self.fs.root_dir(),
        }
    }

    /// Returns file size or 0 for directory.
    #[must_use]
    pub fn len(&self) -> u64 {
        u64::from(self.data.size)
    }

    /// Returns file creation date and time.
    ///
    /// Resolution of the time field is 1/100s.
    #[must_use]
    pub fn created(&self) -> DateTime {
        self.data.created()
    }

    /// Returns file last access date.
    #[must_use]
    pub fn accessed(&self) -> Date {
        self.data.accessed()
    }

    /// Returns file last modification date and time.
    ///
    /// Resolution of the time field is 2s.
    #[must_use]
    pub fn modified(&self) -> DateTime {
        self.data.modified()
    }

    pub(crate) fn raw_short_name(&self) -> &[u8; SFN_SIZE] {
        &self.data.name
    }

    #[cfg(feature = "lfn")]
    fn eq_name_lfn(&self, name: &str) -> bool {
        if let Some(lfn) = self.long_file_name_as_ucs2_units() {
            let self_decode_iter = char::decode_utf16(lfn.iter().copied());
            let mut other_uppercase_iter = name.chars().flat_map(char_to_uppercase);
            for decode_result in self_decode_iter {
                if let Ok(self_char) = decode_result {
                    for self_uppercase_char in char_to_uppercase(self_char) {
                        // compare each character in uppercase
                        if Some(self_uppercase_char) != other_uppercase_iter.next() {
                            return false;
                        }
                    }
                } else {
                    // decoding failed
                    return false;
                }
            }
            // both iterators should be at the end here
            other_uppercase_iter.next().is_none()
        } else {
            // entry has no long name
            false
        }
    }

    pub(crate) fn eq_name(&self, name: &str) -> bool {
        #[cfg(feature = "lfn")]
        {
            if self.eq_name_lfn(name) {
                return true;
            }
        }

        self.short_name.eq_ignore_case(name, &self.fs.options.oem_cp_converter)
    }
}

impl<IO: ReadWriteSeek, TP, OCC> fmt::Debug for DirEntry<'_, IO, TP, OCC> {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        self.data.fmt(f)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::fs::LossyOemCpConverter;

    #[test]
    fn short_name_with_ext() {
        let oem_cp_conv = LossyOemCpConverter::new();
        assert_eq!(ShortName::new(b"FOO     BAR").to_string(&oem_cp_conv), "FOO.BAR");
        assert_eq!(ShortName::new(b"LOOK AT M E").to_string(&oem_cp_conv), "LOOK AT.M E");
        assert_eq!(
            ShortName::new(b"\x99OOK AT M \x99").to_string(&oem_cp_conv),
            "\u{FFFD}OOK AT.M \u{FFFD}"
        );
        assert!(ShortName::new(b"\x99OOK AT M \x99").eq_ignore_case("\u{FFFD}OOK AT.M \u{FFFD}", &oem_cp_conv));
    }

    #[test]
    fn short_name_without_ext() {
        let oem_cp_conv = LossyOemCpConverter::new();
        assert_eq!(ShortName::new(b"FOO        ").to_string(&oem_cp_conv), "FOO");
        assert_eq!(ShortName::new(b"LOOK AT    ").to_string(&oem_cp_conv), "LOOK AT");
    }

    #[test]
    fn short_name_eq_ignore_case() {
        let oem_cp_conv = LossyOemCpConverter::new();
        let raw_short_name: &[u8; SFN_SIZE] = b"\x99OOK AT M \x99";
        assert!(ShortName::new(raw_short_name).eq_ignore_case("\u{FFFD}OOK AT.M \u{FFFD}", &oem_cp_conv));
        assert!(ShortName::new(raw_short_name).eq_ignore_case("\u{FFFD}ook AT.m \u{FFFD}", &oem_cp_conv));
    }

    #[test]
    fn short_name_05_changed_to_e5() {
        let raw_short_name = [0x05; SFN_SIZE];
        assert_eq!(
            ShortName::new(&raw_short_name).as_bytes(),
            [0xE5, 0x05, 0x05, 0x05, 0x05, 0x05, 0x05, 0x05, b'.', 0x05, 0x05, 0x05]
        );
    }

    #[test]
    fn lowercase_short_name() {
        let oem_cp_conv = LossyOemCpConverter::new();
        let raw_short_name: &[u8; SFN_SIZE] = b"FOO     RS ";
        let mut raw_entry = DirFileEntryData {
            name: *raw_short_name,
            reserved_0: (1 << 3) | (1 << 4),
            ..DirFileEntryData::default()
        };
        assert_eq!(raw_entry.lowercase_name().to_string(&oem_cp_conv), "foo.rs");
        raw_entry.reserved_0 = 1 << 3;
        assert_eq!(raw_entry.lowercase_name().to_string(&oem_cp_conv), "foo.RS");
        raw_entry.reserved_0 = 1 << 4;
        assert_eq!(raw_entry.lowercase_name().to_string(&oem_cp_conv), "FOO.rs");
        raw_entry.reserved_0 = 0;
        assert_eq!(raw_entry.lowercase_name().to_string(&oem_cp_conv), "FOO.RS");
    }
}
