#[cfg(all(not(feature = "std"), feature = "alloc"))]
use alloc::string::String;
use core::borrow::BorrowMut;
use core::cell::{Cell, RefCell};
use core::convert::TryFrom;
use core::fmt::Debug;
use core::marker::PhantomData;

use crate::boot_sector::{format_boot_sector, BiosParameterBlock, BootSector};
use crate::dir::{Dir, DirRawStream};
use crate::dir_entry::{DirFileEntryData, FileAttributes, SFN_PADDING, SFN_SIZE};
use crate::error::Error;
use crate::file::File;
use crate::io::{self, IoBase, Read, ReadLeExt, Seek, SeekFrom, Write, WriteLeExt};
use crate::table::{
    alloc_cluster, count_free_clusters, format_fat, read_fat_flags, ClusterIterator, RESERVED_FAT_ENTRIES,
};
use crate::time::{DefaultTimeProvider, TimeProvider};

// FAT implementation based on:
//   http://wiki.osdev.org/FAT
//   https://www.win.tue.nl/~aeb/linux/fs/fat/fat-1.html

/// A type of FAT filesystem.
///
/// `FatType` values are based on the size of File Allocation Table entry.
#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub enum FatType {
    /// 12 bits per FAT entry
    Fat12,
    /// 16 bits per FAT entry
    Fat16,
    /// 32 bits per FAT entry
    Fat32,
}

impl FatType {
    const FAT16_MIN_CLUSTERS: u32 = 4085;
    const FAT32_MIN_CLUSTERS: u32 = 65525;
    const FAT32_MAX_CLUSTERS: u32 = 0x0FFF_FFF4;

    pub(crate) fn from_clusters(total_clusters: u32) -> Self {
        if total_clusters < Self::FAT16_MIN_CLUSTERS {
            FatType::Fat12
        } else if total_clusters < Self::FAT32_MIN_CLUSTERS {
            FatType::Fat16
        } else {
            FatType::Fat32
        }
    }

    pub(crate) fn bits_per_fat_entry(self) -> u32 {
        match self {
            FatType::Fat12 => 12,
            FatType::Fat16 => 16,
            FatType::Fat32 => 32,
        }
    }

    pub(crate) fn min_clusters(self) -> u32 {
        match self {
            FatType::Fat12 => 0,
            FatType::Fat16 => Self::FAT16_MIN_CLUSTERS,
            FatType::Fat32 => Self::FAT32_MIN_CLUSTERS,
        }
    }

    pub(crate) fn max_clusters(self) -> u32 {
        match self {
            FatType::Fat12 => Self::FAT16_MIN_CLUSTERS - 1,
            FatType::Fat16 => Self::FAT32_MIN_CLUSTERS - 1,
            FatType::Fat32 => Self::FAT32_MAX_CLUSTERS,
        }
    }
}

/// A FAT volume status flags retrived from the Boot Sector and the allocation table second entry.
#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub struct FsStatusFlags {
    pub(crate) dirty: bool,
    pub(crate) io_error: bool,
}

impl FsStatusFlags {
    /// Checks if the volume is marked as dirty.
    ///
    /// Dirty flag means volume has been suddenly ejected from filesystem without unmounting.
    #[must_use]
    pub fn dirty(&self) -> bool {
        self.dirty
    }

    /// Checks if the volume has the IO Error flag active.
    #[must_use]
    pub fn io_error(&self) -> bool {
        self.io_error
    }

    fn encode(self) -> u8 {
        let mut res = 0_u8;
        if self.dirty {
            res |= 1;
        }
        if self.io_error {
            res |= 2;
        }
        res
    }

    pub(crate) fn decode(flags: u8) -> Self {
        Self {
            dirty: flags & 1 != 0,
            io_error: flags & 2 != 0,
        }
    }
}

/// A sum of `Read` and `Seek` traits.
pub trait ReadSeek: Read + Seek {}
impl<T: Read + Seek> ReadSeek for T {}

/// A sum of `Read`, `Write` and `Seek` traits.
pub trait ReadWriteSeek: Read + Write + Seek {}
impl<T: Read + Write + Seek> ReadWriteSeek for T {}

#[derive(Clone, Default, Debug)]
struct FsInfoSector {
    free_cluster_count: Option<u32>,
    next_free_cluster: Option<u32>,
    dirty: bool,
}

impl FsInfoSector {
    const LEAD_SIG: u32 = 0x4161_5252;
    const STRUC_SIG: u32 = 0x6141_7272;
    const TRAIL_SIG: u32 = 0xAA55_0000;

    fn deserialize<R: Read>(rdr: &mut R) -> Result<Self, Error<R::Error>> {
        let lead_sig = rdr.read_u32_le()?;
        if lead_sig != Self::LEAD_SIG {
            error!("invalid lead_sig in FsInfo sector: {}", lead_sig);
            return Err(Error::CorruptedFileSystem);
        }
        let mut reserved = [0_u8; 480];
        rdr.read_exact(&mut reserved)?;
        let struc_sig = rdr.read_u32_le()?;
        if struc_sig != Self::STRUC_SIG {
            error!("invalid struc_sig in FsInfo sector: {}", struc_sig);
            return Err(Error::CorruptedFileSystem);
        }
        let free_cluster_count = match rdr.read_u32_le()? {
            0xFFFF_FFFF => None,
            // Note: value is validated in FileSystem::new function using values from BPB
            n => Some(n),
        };
        let next_free_cluster = match rdr.read_u32_le()? {
            0xFFFF_FFFF => None,
            0 | 1 => {
                warn!("invalid next_free_cluster in FsInfo sector (values 0 and 1 are reserved)");
                None
            }
            // Note: other values are validated in FileSystem::new function using values from BPB
            n => Some(n),
        };
        let mut reserved2 = [0_u8; 12];
        rdr.read_exact(&mut reserved2)?;
        let trail_sig = rdr.read_u32_le()?;
        if trail_sig != Self::TRAIL_SIG {
            error!("invalid trail_sig in FsInfo sector: {}", trail_sig);
            return Err(Error::CorruptedFileSystem);
        }
        Ok(Self {
            free_cluster_count,
            next_free_cluster,
            dirty: false,
        })
    }

    fn serialize<W: Write>(&self, wrt: &mut W) -> Result<(), Error<W::Error>> {
        wrt.write_u32_le(Self::LEAD_SIG)?;
        let reserved = [0_u8; 480];
        wrt.write_all(&reserved)?;
        wrt.write_u32_le(Self::STRUC_SIG)?;
        wrt.write_u32_le(self.free_cluster_count.unwrap_or(0xFFFF_FFFF))?;
        wrt.write_u32_le(self.next_free_cluster.unwrap_or(0xFFFF_FFFF))?;
        let reserved2 = [0_u8; 12];
        wrt.write_all(&reserved2)?;
        wrt.write_u32_le(Self::TRAIL_SIG)?;
        Ok(())
    }

    fn validate_and_fix(&mut self, total_clusters: u32) {
        let max_valid_cluster_number = total_clusters + RESERVED_FAT_ENTRIES;
        if let Some(n) = self.free_cluster_count {
            if n > total_clusters {
                warn!(
                    "invalid free_cluster_count ({}) in fs_info exceeds total cluster count ({})",
                    n, total_clusters
                );
                self.free_cluster_count = None;
            }
        }
        if let Some(n) = self.next_free_cluster {
            if n > max_valid_cluster_number {
                warn!(
                    "invalid free_cluster_count ({}) in fs_info exceeds maximum cluster number ({})",
                    n, max_valid_cluster_number
                );
                self.next_free_cluster = None;
            }
        }
    }

    fn map_free_clusters(&mut self, map_fn: impl Fn(u32) -> u32) {
        if let Some(n) = self.free_cluster_count {
            self.free_cluster_count = Some(map_fn(n));
            self.dirty = true;
        }
    }

    fn set_next_free_cluster(&mut self, cluster: u32) {
        self.next_free_cluster = Some(cluster);
        self.dirty = true;
    }

    fn set_free_cluster_count(&mut self, free_cluster_count: u32) {
        self.free_cluster_count = Some(free_cluster_count);
        self.dirty = true;
    }
}

/// A FAT filesystem mount options.
///
/// Options are specified as an argument for `FileSystem::new` method.
#[derive(Copy, Clone, Debug, Default)]
pub struct FsOptions<TP, OCC> {
    pub(crate) update_accessed_date: bool,
    pub(crate) oem_cp_converter: OCC,
    pub(crate) time_provider: TP,
    pub(crate) strict: bool,
}

impl FsOptions<DefaultTimeProvider, LossyOemCpConverter> {
    /// Creates a `FsOptions` struct with default options.
    #[must_use]
    pub fn new() -> Self {
        Self {
            update_accessed_date: false,
            oem_cp_converter: LossyOemCpConverter::new(),
            time_provider: DefaultTimeProvider::new(),
            strict: true,
        }
    }
}

impl<TP: TimeProvider, OCC: OemCpConverter> FsOptions<TP, OCC> {
    /// If enabled accessed date field in directory entry is updated when reading or writing a file.
    #[must_use]
    pub fn update_accessed_date(mut self, enabled: bool) -> Self {
        self.update_accessed_date = enabled;
        self
    }

    /// Changes default OEM code page encoder-decoder.
    pub fn oem_cp_converter<OCC2: OemCpConverter>(self, oem_cp_converter: OCC2) -> FsOptions<TP, OCC2> {
        FsOptions::<TP, OCC2> {
            update_accessed_date: self.update_accessed_date,
            oem_cp_converter,
            time_provider: self.time_provider,
            strict: self.strict,
        }
    }

    /// Changes default time provider.
    pub fn time_provider<TP2: TimeProvider>(self, time_provider: TP2) -> FsOptions<TP2, OCC> {
        FsOptions::<TP2, OCC> {
            update_accessed_date: self.update_accessed_date,
            oem_cp_converter: self.oem_cp_converter,
            time_provider,
            strict: self.strict,
        }
    }

    /// If enabled more validations are performed to check if file-system is conforming to specification.
    pub fn strict(self, strict: bool) -> Self {
        Self {
            update_accessed_date: self.update_accessed_date,
            oem_cp_converter: self.oem_cp_converter,
            time_provider: self.time_provider,
            strict,
        }
    }
}

/// A FAT volume statistics.
#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub struct FileSystemStats {
    cluster_size: u32,
    total_clusters: u32,
    free_clusters: u32,
}

impl FileSystemStats {
    /// Cluster size in bytes
    #[must_use]
    pub fn cluster_size(&self) -> u32 {
        self.cluster_size
    }

    /// Number of total clusters in filesystem usable for file allocation
    #[must_use]
    pub fn total_clusters(&self) -> u32 {
        self.total_clusters
    }

    /// Number of free clusters
    #[must_use]
    pub fn free_clusters(&self) -> u32 {
        self.free_clusters
    }
}

/// A FAT filesystem object.
///
/// `FileSystem` struct is representing a state of a mounted FAT volume.
pub struct FileSystem<IO: ReadWriteSeek, TP = DefaultTimeProvider, OCC = LossyOemCpConverter> {
    pub(crate) disk: RefCell<IO>,
    pub(crate) options: FsOptions<TP, OCC>,
    fat_type: FatType,
    bpb: BiosParameterBlock,
    first_data_sector: u32,
    root_dir_sectors: u32,
    total_clusters: u32,
    fs_info: RefCell<FsInfoSector>,
    current_status_flags: Cell<FsStatusFlags>,
}

pub trait IntoStorage<T: Read + Write + Seek> {
    fn into_storage(self) -> T;
}

impl<T: Read + Write + Seek> IntoStorage<T> for T {
    fn into_storage(self) -> Self {
        self
    }
}

#[cfg(feature = "std")]
impl<T: std::io::Read + std::io::Write + std::io::Seek> IntoStorage<io::StdIoWrapper<T>> for T {
    fn into_storage(self) -> io::StdIoWrapper<Self> {
        io::StdIoWrapper::new(self)
    }
}

impl<IO: Read + Write + Seek, TP, OCC> FileSystem<IO, TP, OCC> {
    /// Creates a new filesystem object instance.
    ///
    /// Supplied `storage` parameter cannot be seeked. If there is a need to read a fragment of disk
    /// image (e.g. partition) library user should wrap the file struct in a struct limiting
    /// access to partition bytes only e.g. `fscommon::StreamSlice`.
    ///
    /// Note: creating multiple filesystem objects with a single underlying storage can
    /// cause a filesystem corruption.
    ///
    /// # Errors
    ///
    /// Errors that can be returned:
    ///
    /// * `Error::CorruptedFileSystem` will be returned if the boot sector and/or the file system information sector
    ///   contains invalid values.
    /// * `Error::Io` will be returned if the provided storage object returned an I/O error.
    ///
    /// # Panics
    ///
    /// Panics in non-optimized build if `storage` position returned by `seek` is not zero.
    pub fn new<T: IntoStorage<IO>>(storage: T, options: FsOptions<TP, OCC>) -> Result<Self, Error<IO::Error>> {
        // Make sure given image is not seeked
        let mut disk = storage.into_storage();
        trace!("FileSystem::new");
        debug_assert!(disk.seek(SeekFrom::Current(0))? == 0);

        // read boot sector
        let bpb = {
            let boot = BootSector::deserialize(&mut disk)?;
            boot.validate(options.strict)?;
            boot.bpb
        };

        let root_dir_sectors = bpb.root_dir_sectors();
        let first_data_sector = bpb.first_data_sector();
        let total_clusters = bpb.total_clusters();
        let fat_type = FatType::from_clusters(total_clusters);

        // read FSInfo sector if this is FAT32
        let mut fs_info = if fat_type == FatType::Fat32 {
            disk.seek(SeekFrom::Start(bpb.bytes_from_sectors(bpb.fs_info_sector())))?;
            FsInfoSector::deserialize(&mut disk)?
        } else {
            FsInfoSector::default()
        };

        // if dirty flag is set completly ignore free_cluster_count in FSInfo
        if bpb.status_flags().dirty {
            fs_info.free_cluster_count = None;
        }

        // Validate the numbers stored in the free_cluster_count and next_free_cluster are within bounds for volume
        fs_info.validate_and_fix(total_clusters);

        // return FileSystem struct
        let status_flags = bpb.status_flags();
        trace!("FileSystem::new end");
        Ok(Self {
            disk: RefCell::new(disk),
            options,
            fat_type,
            bpb,
            first_data_sector,
            root_dir_sectors,
            total_clusters,
            fs_info: RefCell::new(fs_info),
            current_status_flags: Cell::new(status_flags),
        })
    }

    /// Returns a type of File Allocation Table (FAT) used by this filesystem.
    pub fn fat_type(&self) -> FatType {
        self.fat_type
    }

    /// Returns a volume identifier read from BPB in the Boot Sector.
    pub fn volume_id(&self) -> u32 {
        self.bpb.volume_id
    }

    /// Returns a volume label from BPB in the Boot Sector as byte array slice.
    ///
    /// Label is encoded in the OEM codepage.
    /// Note: This function returns label stored in the BPB block. Use `read_volume_label_from_root_dir_as_bytes` to
    /// read label from the root directory.
    pub fn volume_label_as_bytes(&self) -> &[u8] {
        let full_label_slice = &self.bpb.volume_label;
        let len = full_label_slice
            .iter()
            .rposition(|b| *b != SFN_PADDING)
            .map_or(0, |p| p + 1);
        &full_label_slice[..len]
    }

    fn offset_from_sector(&self, sector: u32) -> u64 {
        self.bpb.bytes_from_sectors(sector)
    }

    fn sector_from_cluster(&self, cluster: u32) -> u32 {
        self.first_data_sector + self.bpb.sectors_from_clusters(cluster - RESERVED_FAT_ENTRIES)
    }

    pub fn cluster_size(&self) -> u32 {
        self.bpb.cluster_size()
    }

    pub(crate) fn offset_from_cluster(&self, cluster: u32) -> u64 {
        self.offset_from_sector(self.sector_from_cluster(cluster))
    }

    pub(crate) fn bytes_from_clusters(&self, clusters: u32) -> u64 {
        self.bpb.bytes_from_sectors(self.bpb.sectors_from_clusters(clusters))
    }

    pub(crate) fn clusters_from_bytes(&self, bytes: u64) -> u32 {
        self.bpb.clusters_from_bytes(bytes)
    }

    fn fat_slice(&self) -> impl ReadWriteSeek<Error = Error<IO::Error>> + '_ {
        let io = FsIoAdapter { fs: self };
        fat_slice(io, &self.bpb)
    }

    pub(crate) fn cluster_iter(
        &self,
        cluster: u32,
    ) -> ClusterIterator<impl ReadWriteSeek<Error = Error<IO::Error>> + '_, IO::Error> {
        let disk_slice = self.fat_slice();
        ClusterIterator::new(disk_slice, self.fat_type, cluster)
    }

    pub(crate) fn truncate_cluster_chain(&self, cluster: u32) -> Result<(), Error<IO::Error>> {
        let mut iter = self.cluster_iter(cluster);
        let num_free = iter.truncate()?;
        let mut fs_info = self.fs_info.borrow_mut();
        fs_info.map_free_clusters(|n| n + num_free);
        Ok(())
    }

    pub(crate) fn free_cluster_chain(&self, cluster: u32) -> Result<(), Error<IO::Error>> {
        let mut iter = self.cluster_iter(cluster);
        let num_free = iter.free()?;
        let mut fs_info = self.fs_info.borrow_mut();
        fs_info.map_free_clusters(|n| n + num_free);
        Ok(())
    }

    pub(crate) fn alloc_cluster(&self, prev_cluster: Option<u32>, zero: bool) -> Result<u32, Error<IO::Error>> {
        trace!("alloc_cluster");
        let hint = self.fs_info.borrow().next_free_cluster;
        let cluster = {
            let mut fat = self.fat_slice();
            alloc_cluster(&mut fat, self.fat_type, prev_cluster, hint, self.total_clusters)?
        };
        if zero {
            let mut disk = self.disk.borrow_mut();
            disk.seek(SeekFrom::Start(self.offset_from_cluster(cluster)))?;
            write_zeros(&mut *disk, u64::from(self.cluster_size()))?;
        }
        let mut fs_info = self.fs_info.borrow_mut();
        fs_info.set_next_free_cluster(cluster + 1);
        fs_info.map_free_clusters(|n| n - 1);
        Ok(cluster)
    }

    /// Returns status flags for this volume.
    ///
    /// # Errors
    ///
    /// `Error::Io` will be returned if the underlying storage object returned an I/O error.
    pub fn read_status_flags(&self) -> Result<FsStatusFlags, Error<IO::Error>> {
        let bpb_status = self.bpb.status_flags();
        let fat_status = read_fat_flags(&mut self.fat_slice(), self.fat_type)?;
        Ok(FsStatusFlags {
            dirty: bpb_status.dirty || fat_status.dirty,
            io_error: bpb_status.io_error || fat_status.io_error,
        })
    }

    /// Returns filesystem statistics like number of total and free clusters.
    ///
    /// For FAT32 volumes number of free clusters from the FS Information Sector is returned (may be incorrect).
    /// For other FAT variants number is computed on the first call to this method and cached for later use.
    ///
    /// # Errors
    ///
    /// `Error::Io` will be returned if the underlying storage object returned an I/O error.
    pub fn stats(&self) -> Result<FileSystemStats, Error<IO::Error>> {
        let free_clusters_option = self.fs_info.borrow().free_cluster_count;
        let free_clusters = if let Some(n) = free_clusters_option {
            n
        } else {
            self.recalc_free_clusters()?
        };
        Ok(FileSystemStats {
            cluster_size: self.cluster_size(),
            total_clusters: self.total_clusters,
            free_clusters,
        })
    }

    /// Forces free clusters recalculation.
    fn recalc_free_clusters(&self) -> Result<u32, Error<IO::Error>> {
        let mut fat = self.fat_slice();
        let free_cluster_count = count_free_clusters(&mut fat, self.fat_type, self.total_clusters)?;
        self.fs_info.borrow_mut().set_free_cluster_count(free_cluster_count);
        Ok(free_cluster_count)
    }

    /// Unmounts the filesystem.
    ///
    /// Updates the FS Information Sector if needed.
    ///
    /// # Errors
    ///
    /// `Error::Io` will be returned if the underlying storage object returned an I/O error.
    pub fn unmount(self) -> Result<(), Error<IO::Error>> {
        self.unmount_internal()
    }

    fn unmount_internal(&self) -> Result<(), Error<IO::Error>> {
        self.flush_fs_info()?;
        self.set_dirty_flag(false)?;
        Ok(())
    }

    pub fn flush_fs_info(&self) -> Result<(), Error<IO::Error>> {
        let mut fs_info = self.fs_info.borrow_mut();
        if self.fat_type == FatType::Fat32 && fs_info.dirty {
            let mut disk = self.disk.borrow_mut();
            let fs_info_sector_offset = self.offset_from_sector(u32::from(self.bpb.fs_info_sector));
            disk.seek(SeekFrom::Start(fs_info_sector_offset))?;
            fs_info.serialize(&mut *disk)?;
            fs_info.dirty = false;
        }
        Ok(())
    }

    pub(crate) fn set_dirty_flag(&self, dirty: bool) -> Result<(), IO::Error> {
        // Do not overwrite flags read from BPB on mount
        let mut flags = self.bpb.status_flags();
        flags.dirty |= dirty;
        // Check if flags has changed
        let current_flags = self.current_status_flags.get();
        if flags == current_flags {
            // Nothing to do
            return Ok(());
        }
        let encoded = flags.encode();
        // Note: only one field is written to avoid rewriting entire boot-sector which could be dangerous
        // Compute reserver_1 field offset and write new flags
        let offset = if self.fat_type() == FatType::Fat32 {
            0x041
        } else {
            0x025
        };
        let mut disk = self.disk.borrow_mut();
        disk.seek(io::SeekFrom::Start(offset))?;
        disk.write_u8(encoded)?;
        self.current_status_flags.set(flags);
        Ok(())
    }

    /// Returns a root directory object allowing for futher penetration of a filesystem structure.
    pub fn root_dir(&self) -> Dir<IO, TP, OCC> {
        trace!("root_dir");
        let root_rdr = {
            match self.fat_type {
                FatType::Fat12 | FatType::Fat16 => DirRawStream::Root(DiskSlice::from_sectors(
                    self.first_data_sector - self.root_dir_sectors,
                    self.root_dir_sectors,
                    1,
                    &self.bpb,
                    FsIoAdapter { fs: self },
                )),
                FatType::Fat32 => DirRawStream::File(File::new(Some(self.bpb.root_dir_first_cluster), None, self)),
            }
        };
        Dir::new(root_rdr, self)
    }

    pub fn total_clusters(&self) -> u32 {
        self.total_clusters
    }
}

impl<IO: ReadWriteSeek, TP, OCC: OemCpConverter> FileSystem<IO, TP, OCC> {
    /// Returns a volume label from BPB in the Boot Sector as `String`.
    ///
    /// Non-ASCII characters are replaced by the replacement character (U+FFFD).
    /// Note: This function returns label stored in the BPB block. Use `read_volume_label_from_root_dir` to read label
    /// from the root directory.
    #[cfg(feature = "alloc")]
    pub fn volume_label(&self) -> String {
        // Decode volume label from OEM codepage
        let volume_label_iter = self.volume_label_as_bytes().iter().copied();
        let char_iter = volume_label_iter.map(|c| self.options.oem_cp_converter.decode(c));
        // Build string from character iterator
        char_iter.collect()
    }
}

impl<IO: ReadWriteSeek, TP: TimeProvider, OCC: OemCpConverter> FileSystem<IO, TP, OCC> {
    /// Returns a volume label from root directory as `String`.
    ///
    /// It finds file with `VOLUME_ID` attribute and returns its short name.
    ///
    /// # Errors
    ///
    /// `Error::Io` will be returned if the underlying storage object returned an I/O error.
    #[cfg(feature = "alloc")]
    pub fn read_volume_label_from_root_dir(&self) -> Result<Option<String>, Error<IO::Error>> {
        // Note: DirEntry::file_short_name() cannot be used because it interprets name as 8.3
        // (adds dot before an extension)
        let volume_label_opt = self.read_volume_label_from_root_dir_as_bytes()?;
        volume_label_opt.map_or(Ok(None), |volume_label| {
            // Strip label padding
            let len = volume_label
                .iter()
                .rposition(|b| *b != SFN_PADDING)
                .map_or(0, |p| p + 1);
            let label_slice = &volume_label[..len];
            // Decode volume label from OEM codepage
            let volume_label_iter = label_slice.iter().copied();
            let char_iter = volume_label_iter.map(|c| self.options.oem_cp_converter.decode(c));
            // Build string from character iterator
            Ok(Some(char_iter.collect::<String>()))
        })
    }

    /// Returns a volume label from root directory as byte array.
    ///
    /// Label is encoded in the OEM codepage.
    /// It finds file with `VOLUME_ID` attribute and returns its short name.
    ///
    /// # Errors
    ///
    /// `Error::Io` will be returned if the underlying storage object returned an I/O error.
    pub fn read_volume_label_from_root_dir_as_bytes(&self) -> Result<Option<[u8; SFN_SIZE]>, Error<IO::Error>> {
        let entry_opt = self.root_dir().find_volume_entry()?;
        Ok(entry_opt.map(|e| *e.raw_short_name()))
    }
}

/// `Drop` implementation tries to unmount the filesystem when dropping.
impl<IO: ReadWriteSeek, TP, OCC> Drop for FileSystem<IO, TP, OCC> {
    fn drop(&mut self) {
        if let Err(err) = self.unmount_internal() {
            error!("unmount failed {:?}", err);
        }
    }
}

pub(crate) struct FsIoAdapter<'a, IO: ReadWriteSeek, TP, OCC> {
    fs: &'a FileSystem<IO, TP, OCC>,
}

impl<IO: ReadWriteSeek, TP, OCC> IoBase for FsIoAdapter<'_, IO, TP, OCC> {
    type Error = IO::Error;
}

impl<IO: ReadWriteSeek, TP, OCC> Read for FsIoAdapter<'_, IO, TP, OCC> {
    fn read(&mut self, buf: &mut [u8]) -> Result<usize, Self::Error> {
        self.fs.disk.borrow_mut().read(buf)
    }
}

impl<IO: ReadWriteSeek, TP, OCC> Write for FsIoAdapter<'_, IO, TP, OCC> {
    fn write(&mut self, buf: &[u8]) -> Result<usize, Self::Error> {
        let size = self.fs.disk.borrow_mut().write(buf)?;
        if size > 0 {
            self.fs.set_dirty_flag(true)?;
        }
        Ok(size)
    }

    fn flush(&mut self) -> Result<(), Self::Error> {
        self.fs.disk.borrow_mut().flush()
    }
}

impl<IO: ReadWriteSeek, TP, OCC> Seek for FsIoAdapter<'_, IO, TP, OCC> {
    fn seek(&mut self, pos: SeekFrom) -> Result<u64, Self::Error> {
        self.fs.disk.borrow_mut().seek(pos)
    }
}

// Note: derive cannot be used because of invalid bounds. See: https://github.com/rust-lang/rust/issues/26925
impl<IO: ReadWriteSeek, TP, OCC> Clone for FsIoAdapter<'_, IO, TP, OCC> {
    fn clone(&self) -> Self {
        FsIoAdapter { fs: self.fs }
    }
}

fn fat_slice<S: ReadWriteSeek, B: BorrowMut<S>>(
    io: B,
    bpb: &BiosParameterBlock,
) -> impl ReadWriteSeek<Error = Error<S::Error>> {
    let sectors_per_fat = bpb.sectors_per_fat();
    let mirroring_enabled = bpb.mirroring_enabled();
    let (fat_first_sector, mirrors) = if mirroring_enabled {
        (bpb.reserved_sectors(), bpb.fats)
    } else {
        let active_fat = u32::from(bpb.active_fat());
        let fat_first_sector = (bpb.reserved_sectors()) + active_fat * sectors_per_fat;
        (fat_first_sector, 1)
    };
    DiskSlice::from_sectors(fat_first_sector, sectors_per_fat, mirrors, bpb, io)
}

pub(crate) struct DiskSlice<B, S = B> {
    begin: u64,
    size: u64,
    offset: u64,
    mirrors: u8,
    inner: B,
    phantom: PhantomData<S>,
}

impl<B: BorrowMut<S>, S: ReadWriteSeek> DiskSlice<B, S> {
    pub(crate) fn new(begin: u64, size: u64, mirrors: u8, inner: B) -> Self {
        Self {
            begin,
            size,
            mirrors,
            inner,
            offset: 0,
            phantom: PhantomData,
        }
    }

    fn from_sectors(first_sector: u32, sector_count: u32, mirrors: u8, bpb: &BiosParameterBlock, inner: B) -> Self {
        Self::new(
            bpb.bytes_from_sectors(first_sector),
            bpb.bytes_from_sectors(sector_count),
            mirrors,
            inner,
        )
    }

    pub(crate) fn abs_pos(&self) -> u64 {
        self.begin + self.offset
    }
}

// Note: derive cannot be used because of invalid bounds. See: https://github.com/rust-lang/rust/issues/26925
impl<B: Clone, S> Clone for DiskSlice<B, S> {
    fn clone(&self) -> Self {
        Self {
            begin: self.begin,
            size: self.size,
            offset: self.offset,
            mirrors: self.mirrors,
            inner: self.inner.clone(),
            // phantom is needed to add type bounds on the storage type
            phantom: PhantomData,
        }
    }
}

impl<B, S: IoBase> IoBase for DiskSlice<B, S> {
    type Error = Error<S::Error>;
}

impl<B: BorrowMut<S>, S: Read + Seek> Read for DiskSlice<B, S> {
    fn read(&mut self, buf: &mut [u8]) -> Result<usize, Self::Error> {
        let offset = self.begin + self.offset;
        let read_size = (buf.len() as u64).min(self.size - self.offset) as usize;
        self.inner.borrow_mut().seek(SeekFrom::Start(offset))?;
        let size = self.inner.borrow_mut().read(&mut buf[..read_size])?;
        self.offset += size as u64;
        Ok(size)
    }
}

impl<B: BorrowMut<S>, S: Write + Seek> Write for DiskSlice<B, S> {
    fn write(&mut self, buf: &[u8]) -> Result<usize, Self::Error> {
        let offset = self.begin + self.offset;
        let write_size = (buf.len() as u64).min(self.size - self.offset) as usize;
        if write_size == 0 {
            return Ok(0);
        }
        // Write data
        let storage = self.inner.borrow_mut();
        for i in 0..self.mirrors {
            storage.seek(SeekFrom::Start(offset + u64::from(i) * self.size))?;
            storage.write_all(&buf[..write_size])?;
        }
        self.offset += write_size as u64;
        Ok(write_size)
    }

    fn flush(&mut self) -> Result<(), Self::Error> {
        Ok(self.inner.borrow_mut().flush()?)
    }
}

impl<B, S: IoBase> Seek for DiskSlice<B, S> {
    fn seek(&mut self, pos: SeekFrom) -> Result<u64, Self::Error> {
        let new_offset_opt: Option<u64> = match pos {
            SeekFrom::Current(x) => i64::try_from(self.offset)
                .ok()
                .and_then(|n| n.checked_add(x))
                .and_then(|n| u64::try_from(n).ok()),
            SeekFrom::Start(x) => Some(x),
            SeekFrom::End(o) => i64::try_from(self.size)
                .ok()
                .and_then(|size| size.checked_add(o))
                .and_then(|n| u64::try_from(n).ok()),
        };
        if let Some(new_offset) = new_offset_opt {
            if new_offset > self.size {
                error!("Seek beyond the end of the file");
                Err(Error::InvalidInput)
            } else {
                self.offset = new_offset;
                Ok(self.offset)
            }
        } else {
            error!("Invalid seek offset");
            Err(Error::InvalidInput)
        }
    }
}

/// An OEM code page encoder/decoder.
///
/// Provides a custom implementation for a short name encoding/decoding.
/// `OemCpConverter` is specified by the `oem_cp_converter` property in `FsOptions` struct.
pub trait OemCpConverter: Debug {
    fn decode(&self, oem_char: u8) -> char;
    fn encode(&self, uni_char: char) -> Option<u8>;
}

/// Default implementation of `OemCpConverter` that changes all non-ASCII characters to the replacement character (U+FFFD).
#[derive(Debug, Clone, Copy, Default)]
pub struct LossyOemCpConverter {
    _dummy: (),
}

impl LossyOemCpConverter {
    #[must_use]
    pub fn new() -> Self {
        Self { _dummy: () }
    }
}

impl OemCpConverter for LossyOemCpConverter {
    fn decode(&self, oem_char: u8) -> char {
        if oem_char <= 0x7F {
            char::from(oem_char)
        } else {
            '\u{FFFD}'
        }
    }
    fn encode(&self, uni_char: char) -> Option<u8> {
        if uni_char <= '\x7F' {
            Some(uni_char as u8) // safe cast: value is in range [0, 0x7F]
        } else {
            None
        }
    }
}

pub(crate) fn write_zeros<IO: ReadWriteSeek>(disk: &mut IO, mut len: u64) -> Result<(), IO::Error> {
    const ZEROS: [u8; 512] = [0_u8; 512];
    while len > 0 {
        let write_size = len.min(ZEROS.len() as u64) as usize;
        disk.write_all(&ZEROS[..write_size])?;
        len -= write_size as u64;
    }
    Ok(())
}

fn write_zeros_until_end_of_sector<IO: ReadWriteSeek>(disk: &mut IO, bytes_per_sector: u16) -> Result<(), IO::Error> {
    let pos = disk.seek(SeekFrom::Current(0))?;
    let total_bytes_to_write = u64::from(bytes_per_sector) - (pos % u64::from(bytes_per_sector));
    if total_bytes_to_write != u64::from(bytes_per_sector) {
        write_zeros(disk, total_bytes_to_write)?;
    }
    Ok(())
}

/// A FAT filesystem formatting options
///
/// This struct implements a builder pattern.
/// Options are specified as an argument for `format_volume` function.
#[derive(Debug, Clone)]
pub struct FormatVolumeOptions {
    pub(crate) bytes_per_sector: u16,
    pub(crate) total_sectors: Option<u32>,
    pub(crate) bytes_per_cluster: Option<u32>,
    pub(crate) fat_type: Option<FatType>,
    pub(crate) max_root_dir_entries: u16,
    pub(crate) fats: u8,
    pub(crate) media: u8,
    pub(crate) sectors_per_track: u16,
    pub(crate) heads: u16,
    pub(crate) drive_num: Option<u8>,
    pub(crate) volume_id: u32,
    pub(crate) volume_label: Option<[u8; SFN_SIZE]>,
}

impl Default for FormatVolumeOptions {
    fn default() -> Self {
        Self {
            bytes_per_sector: 512,
            total_sectors: None,
            bytes_per_cluster: None,
            fat_type: None,
            max_root_dir_entries: 512,
            fats: 2,
            media: 0xF8,
            sectors_per_track: 0x20,
            heads: 0x40,
            drive_num: None,
            volume_id: 0x1234_5678,
            volume_label: None,
        }
    }
}

impl FormatVolumeOptions {
    /// Create options struct for `format_volume` function
    ///
    /// Allows to overwrite many filesystem parameters.
    /// In normal use-case defaults should suffice.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Set size of cluster in bytes (must be dividable by sector size)
    ///
    /// Cluster size must be a power of two and be greater or equal to sector size.
    /// If option is not specified optimal cluster size is selected based on partition size and
    /// optionally FAT type override (if specified using `fat_type` method).
    ///
    /// # Panics
    ///
    /// Panics if `bytes_per_cluster` is not a power of two or is lower than `512`.
    #[must_use]
    pub fn bytes_per_cluster(mut self, bytes_per_cluster: u32) -> Self {
        assert!(
            bytes_per_cluster.is_power_of_two() && bytes_per_cluster >= 512,
            "Invalid bytes_per_cluster"
        );
        self.bytes_per_cluster = Some(bytes_per_cluster);
        self
    }

    /// Set File Allocation Table type
    ///
    /// Option allows to override File Allocation Table (FAT) entry size.
    /// It is unrecommended to set this option unless you know what you are doing.
    /// Note: FAT type is determined from total number of clusters. Changing this option can cause formatting to fail
    /// if the volume cannot be divided into proper number of clusters for selected FAT type.
    #[must_use]
    pub fn fat_type(mut self, fat_type: FatType) -> Self {
        self.fat_type = Some(fat_type);
        self
    }

    /// Set sector size in bytes
    ///
    /// Sector size must be a power of two and be in range 512 - 4096.
    /// Default is `512`.
    ///
    /// # Panics
    ///
    /// Panics if `bytes_per_sector` is not a power of two or is lower than `512`.
    #[must_use]
    pub fn bytes_per_sector(mut self, bytes_per_sector: u16) -> Self {
        assert!(
            bytes_per_sector.is_power_of_two() && bytes_per_sector >= 512,
            "Invalid bytes_per_sector"
        );
        self.bytes_per_sector = bytes_per_sector;
        self
    }

    /// Set total number of sectors
    ///
    /// If option is not specified total number of sectors is calculated as storage device size divided by sector size.
    #[must_use]
    pub fn total_sectors(mut self, total_sectors: u32) -> Self {
        self.total_sectors = Some(total_sectors);
        self
    }

    /// Set maximal numer of entries in root directory for FAT12/FAT16 volumes
    ///
    /// Total root directory size should be dividable by sectors size so keep it a multiple of 16 (for default sector
    /// size).
    /// Note: this limit is not used on FAT32 volumes.
    /// Default is `512`.
    #[must_use]
    pub fn max_root_dir_entries(mut self, max_root_dir_entries: u16) -> Self {
        self.max_root_dir_entries = max_root_dir_entries;
        self
    }

    /// Set number of File Allocation Tables
    ///
    /// The only allowed values are `1` and `2`. If value `2` is used the FAT is mirrored.
    /// Default is `2`.
    ///
    /// # Panics
    ///
    /// Panics if `fats` is outside of the range [1, 2].
    #[must_use]
    pub fn fats(mut self, fats: u8) -> Self {
        assert!((1..=2).contains(&fats), "Invalid number of FATs");
        self.fats = fats;
        self
    }

    /// Set media field for Bios Parameters Block
    ///
    /// Default is `0xF8`.
    #[must_use]
    pub fn media(mut self, media: u8) -> Self {
        self.media = media;
        self
    }

    /// Set number of physical sectors per track for Bios Parameters Block (INT 13h CHS geometry)
    ///
    /// Default is `0x20`.
    #[must_use]
    pub fn sectors_per_track(mut self, sectors_per_track: u16) -> Self {
        self.sectors_per_track = sectors_per_track;
        self
    }

    /// Set number of heads for Bios Parameters Block (INT 13h CHS geometry)
    ///
    /// Default is `0x40`.
    #[must_use]
    pub fn heads(mut self, heads: u16) -> Self {
        self.heads = heads;
        self
    }

    /// Set drive number for Bios Parameters Block
    ///
    /// Default is `0` for FAT12, `0x80` for FAT16/FAT32.
    #[must_use]
    pub fn drive_num(mut self, drive_num: u8) -> Self {
        self.drive_num = Some(drive_num);
        self
    }

    /// Set volume ID for Bios Parameters Block
    ///
    /// Default is `0x12345678`.
    #[must_use]
    pub fn volume_id(mut self, volume_id: u32) -> Self {
        self.volume_id = volume_id;
        self
    }

    /// Set volume label
    ///
    /// Default is empty label.
    #[must_use]
    pub fn volume_label(mut self, volume_label: [u8; SFN_SIZE]) -> Self {
        self.volume_label = Some(volume_label);
        self
    }
}

/// Create FAT filesystem on a disk or partition (format a volume)
///
/// Warning: this function overrides internal FAT filesystem structures and causes a loss of all data on provided
/// partition. Please use it with caution.
/// Only quick formatting is supported. To achieve a full format zero entire partition before calling this function.
/// Supplied `storage` parameter cannot be seeked (internal pointer must be on position 0).
/// To format a fragment of a disk image (e.g. partition) library user should wrap the file struct in a struct
/// limiting access to partition bytes only e.g. `fscommon::StreamSlice`.
///
/// # Errors
///
/// Errors that can be returned:
///
/// * `Error::InvalidInput` will be returned if `options` describes an invalid file system that cannot be created.
///   Possible reason can be requesting a fat type that is not compatible with the total number of clusters or
///   formatting a too big storage. If sectors/clusters related options in `options` structure were left set to
///   defaults this error is very unlikely to happen.
/// * `Error::Io` will be returned if the provided storage object returned an I/O error.
///
/// # Panics
///
/// Panics in non-optimized build if `storage` position returned by `seek` is not zero.
#[allow(clippy::needless_pass_by_value)]
pub fn format_volume<S: ReadWriteSeek>(storage: &mut S, options: FormatVolumeOptions) -> Result<(), Error<S::Error>> {
    trace!("format_volume");
    debug_assert!(storage.seek(SeekFrom::Current(0))? == 0);

    let total_sectors = if let Some(total_sectors) = options.total_sectors {
        total_sectors
    } else {
        let total_bytes: u64 = storage.seek(SeekFrom::End(0))?;
        let total_sectors_64 = total_bytes / u64::from(options.bytes_per_sector);
        storage.seek(SeekFrom::Start(0))?;
        if total_sectors_64 > u64::from(u32::MAX) {
            error!("Volume has too many sectors: {}", total_sectors_64);
            return Err(Error::InvalidInput);
        }
        total_sectors_64 as u32 // safe case: possible overflow is handled above
    };

    // Create boot sector, validate and write to storage device
    let (boot, fat_type) = format_boot_sector(&options, total_sectors)?;
    if boot.validate::<S::Error>(true).is_err() {
        return Err(Error::InvalidInput);
    }
    boot.serialize(storage)?;
    // Make sure entire logical sector is updated (serialize method always writes 512 bytes)
    let bytes_per_sector = boot.bpb.bytes_per_sector;
    write_zeros_until_end_of_sector(storage, bytes_per_sector)?;

    let bpb = &boot.bpb;
    if bpb.is_fat32() {
        // FSInfo sector
        let fs_info_sector = FsInfoSector {
            free_cluster_count: None,
            next_free_cluster: None,
            dirty: false,
        };
        storage.seek(SeekFrom::Start(bpb.bytes_from_sectors(bpb.fs_info_sector())))?;
        fs_info_sector.serialize(storage)?;
        write_zeros_until_end_of_sector(storage, bytes_per_sector)?;

        // backup boot sector
        storage.seek(SeekFrom::Start(bpb.bytes_from_sectors(bpb.backup_boot_sector())))?;
        boot.serialize(storage)?;
        write_zeros_until_end_of_sector(storage, bytes_per_sector)?;
    }

    // format File Allocation Table
    let reserved_sectors = bpb.reserved_sectors();
    let fat_pos = bpb.bytes_from_sectors(reserved_sectors);
    let sectors_per_all_fats = bpb.sectors_per_all_fats();
    storage.seek(SeekFrom::Start(fat_pos))?;
    write_zeros(storage, bpb.bytes_from_sectors(sectors_per_all_fats))?;
    {
        let mut fat_slice = fat_slice::<S, &mut S>(storage, bpb);
        let sectors_per_fat = bpb.sectors_per_fat();
        let bytes_per_fat = bpb.bytes_from_sectors(sectors_per_fat);
        format_fat(&mut fat_slice, fat_type, bpb.media, bytes_per_fat, bpb.total_clusters())?;
    }

    // init root directory - zero root directory region for FAT12/16 and alloc first root directory cluster for FAT32
    let root_dir_first_sector = reserved_sectors + sectors_per_all_fats;
    let root_dir_sectors = bpb.root_dir_sectors();
    let root_dir_pos = bpb.bytes_from_sectors(root_dir_first_sector);
    storage.seek(SeekFrom::Start(root_dir_pos))?;
    write_zeros(storage, bpb.bytes_from_sectors(root_dir_sectors))?;
    if fat_type == FatType::Fat32 {
        let root_dir_first_cluster = {
            let mut fat_slice = fat_slice::<S, &mut S>(storage, bpb);
            alloc_cluster(&mut fat_slice, fat_type, None, None, 1)?
        };
        assert!(root_dir_first_cluster == bpb.root_dir_first_cluster);
        let first_data_sector = reserved_sectors + sectors_per_all_fats + root_dir_sectors;
        let data_sectors_before_root_dir = bpb.sectors_from_clusters(root_dir_first_cluster - RESERVED_FAT_ENTRIES);
        let fat32_root_dir_first_sector = first_data_sector + data_sectors_before_root_dir;
        let fat32_root_dir_pos = bpb.bytes_from_sectors(fat32_root_dir_first_sector);
        storage.seek(SeekFrom::Start(fat32_root_dir_pos))?;
        write_zeros(storage, u64::from(bpb.cluster_size()))?;
    }

    // Create volume label directory entry if volume label is specified in options
    if let Some(volume_label) = options.volume_label {
        storage.seek(SeekFrom::Start(root_dir_pos))?;
        let volume_entry = DirFileEntryData::new(volume_label, FileAttributes::VOLUME_ID);
        volume_entry.serialize(storage)?;
    }

    storage.seek(SeekFrom::Start(0))?;
    trace!("format_volume end");
    Ok(())
}
