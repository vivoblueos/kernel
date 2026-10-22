use crate::prelude::*;
/// Reuse the POSIX-2001 `timespec` from `unix/mod.rs` so that `libc::timespec`
/// and the type used by `futimens` / `utimensat` are the same type.
pub use crate::timespec;

/// BlueOS's libc is supposed to support POSIX.1-2001.
pub type clock_t = c_long;

pub type wchar_t = u32;

pub type sigset_t = c_ulong;
pub type timer_t = c_int;

// Fixed-width types for wireless extensions
pub type __u8 = c_uchar;
pub type __u16 = c_ushort;
pub type __s16 = c_short;
pub type __u32 = c_uint;
pub type __s32 = c_int;
pub const IFNAMSIZ: usize = 16;

s! {
    pub struct itimerspec {
        pub it_interval: crate::timespec,
        pub it_value: crate::timespec,
    }
    // reuse linux sigevent definition
    pub struct sigevent {
        pub sigev_value: crate::sigval,
        pub sigev_signo: c_int,
        pub sigev_notify: c_int,
        // Actually a union.  We only expose sigev_notify_thread_id because it's
        // the most useful member
        pub sigev_notify_thread_id: c_int,
        #[cfg(target_pointer_width = "64")]
        __unused1: [c_int; 11],
        #[cfg(target_pointer_width = "32")]
        __unused1: [c_int; 12],
    }

    pub struct dirent {
        pub d_ino: crate::ino_t,
        pub d_off: crate::off_t,
        pub d_reclen: c_ushort,
        pub d_type: c_uchar,
        pub d_namlen: c_ushort,
        pub d_name: [c_char; 256],
    }

    pub struct msghdr {
        pub msg_name: *mut c_void,
        pub msg_namelen: crate::socklen_t,
        pub msg_iov: *mut crate::iovec,
        pub msg_iovlen: c_int,
        pub msg_control: *mut c_void,
        pub msg_controllen: crate::socklen_t,
        pub msg_flags: c_int,
    }

    pub struct sockaddr {
        pub sa_len: u8,
        pub sa_family: crate::sa_family_t,
        pub sa_data: [c_char; 14],
    }

    pub struct sockaddr_in6 {
        pub sin6_len: u8,
        pub sin6_family: crate::sa_family_t,
        pub sin6_port: crate::in_port_t,
        pub sin6_flowinfo: u32,
        pub sin6_addr: crate::in6_addr,
        pub sin6_vport: crate::in_port_t,
        pub sin6_scope_id: u32,
    }

    pub struct sockaddr_in {
        pub sin_len: u8,
        pub sin_family: crate::sa_family_t,
        pub sin_port: crate::in_port_t,
        pub sin_addr: crate::in_addr,
        pub sin_vport: crate::in_port_t,
        pub sin_zero: [u8; 6],
    }

    pub struct sockaddr_un {
        pub ss_len: u8,
        pub sun_family: crate::sa_family_t,
        pub sun_path: [c_char; 108usize],
    }

    pub struct sockaddr_storage {
        pub ss_len: u8,
        pub ss_family: crate::sa_family_t,
        pub __ss_pad1: [u8; 2],
        pub __ss_align: i64,
        pub __ss_pad2: [u8; 116],
    }

    pub struct sched_param {
        pub sched_priority: c_int,
    }

    pub struct stat {
        pub st_dev: crate::dev_t,
        pub st_ino: crate::ino_t,
        pub st_mode: crate::mode_t,
        pub st_nlink: crate::nlink_t,
        pub st_uid: crate::uid_t,
        pub st_gid: crate::gid_t,
        pub st_rdev: crate::dev_t,
        pub st_size: crate::off_t,
        __st_size_padding: c_int,
        pub st_atim: crate::timespec,
        pub st_mtim: crate::timespec,
        pub st_ctim: crate::timespec,
        pub st_blksize: crate::blksize_t,
        pub st_blocks: crate::blkcnt_t,
        __st_spare: [c_int; 2usize],
    }

    pub struct statfs {
        pub f_type: c_ulong,
        pub f_bsize: c_ulong,
        pub f_blocks: crate::fsblkcnt_t,
        pub f_bfree: crate::fsblkcnt_t,
        pub f_bavail: crate::fsblkcnt_t,
        pub f_files: crate::fsfilcnt_t,
        pub f_ffree: crate::fsfilcnt_t,
        pub f_fsid: u64,
        pub f_namelen: c_ulong,
        pub f_frsize: c_ulong,
        pub f_flags: c_ulong,
        pub f_spare: [c_ulong; 4],
    }

    pub struct fb_bitfield {
        pub offset: u32,
        pub length: u32,
        pub msb_right: u32,
    }

    pub struct fb_fix_screeninfo {
        pub id: [c_char; 16],
        pub smem_start: c_ulong,
        pub smem_len: u32,
        pub type_: u32,
        pub type_aux: u32,
        pub visual: u32,
        pub xpanstep: u16,
        pub ypanstep: u16,
        pub ywrapstep: u16,
        pub line_length: u32,
        pub mmio_start: c_ulong,
        pub mmio_len: u32,
        pub accel: u32,
        pub capabilities: u16,
        pub reserved: [u16; 2],
        __reserved: [u8; 12],
    }

    pub struct fb_var_screeninfo {
        pub xres: u32,
        pub yres: u32,
        pub xres_virtual: u32,
        pub yres_virtual: u32,
        pub xoffset: u32,
        pub yoffset: u32,
        pub bits_per_pixel: u32,
        pub grayscale: u32,
        pub red: fb_bitfield,
        pub green: fb_bitfield,
        pub blue: fb_bitfield,
        pub transp: fb_bitfield,
        pub nonstd: u32,
        pub activate: u32,
        pub height: u32,
        pub width: u32,
        pub accel_flags: u32,
        pub pixclock: u32,
        pub left_margin: u32,
        pub right_margin: u32,
        pub upper_margin: u32,
        pub lower_margin: u32,
        pub hsync_len: u32,
        pub vsync_len: u32,
        pub sync: u32,
        pub vmode: u32,
        pub rotate: u32,
        pub colorspace: u32,
        pub reserved: [u32; 4],
    }

    pub struct pthread_barrier_t {
        #[cfg(target_pointer_width = "32")]
        pub __librs_internal_size: [c_uchar; 24],
        #[cfg(target_pointer_width = "64")]
        pub __librs_internal_size: [c_uchar; 40],
        pub __librs_internal_align: [c_ulonglong; 0],
    }

    pub struct pthread_barrierattr_t {
        pub __librs_internal_size: [c_uchar; 4],
        pub __librs_internal_align: [c_int; 0],
    }
}
// ---- Wireless extensions (linux/wireless.h) ----

s! {
    pub struct iw_param {
        pub value: __s32,
        pub fixed: __u8,
        pub disabled: __u8,
        pub flags: __u16,
    }

    pub struct iw_point {
        pub pointer: *mut c_void,
        pub length: __u16,
        pub flags: __u16,
    }

    pub struct iw_freq {
        pub m: __s32,
        pub e: __s16,
        pub i: __u8,
        pub flags: __u8,
    }

    pub struct iw_quality {
        pub qual: __u8,
        pub level: __u8,
        pub noise: __u8,
        pub updated: __u8,
    }

    pub struct iw_scan_req {
        pub scan_type: __u8,
        pub essid_len: __u8,
        pub num_channels: __u8,
        pub flags: __u8,
        pub bssid: sockaddr,
        pub essid: [__u8; IW_ESSID_MAX_SIZE],
        pub min_channel_time: __u32,
        pub max_channel_time: __u32,
        pub channel_list: [iw_freq; IW_MAX_FREQUENCIES],
    }
}

s_no_extra_traits! {
    pub union iwreq_data {
        pub name: [c_char; IFNAMSIZ],
        pub essid: iw_point,
        pub nwid: iw_param,
        pub freq: iw_freq,
        pub sens: iw_param,
        pub bitrate: iw_param,
        pub txpower: iw_param,
        pub rts: iw_param,
        pub frag: iw_param,
        pub mode: __u32,
        pub retry: iw_param,
        pub encoding: iw_point,
        pub power: iw_param,
        pub qual: iw_quality,
        pub ap_addr: sockaddr,
        pub addr: sockaddr,
        pub param: iw_param,
        pub data: iw_point,
    }

    pub union __c_anonymous_iwreq {
        pub ifrn_name: [c_char; IFNAMSIZ],
    }

    pub struct iwreq {
        pub ifr_ifrn: __c_anonymous_iwreq,
        pub u: iwreq_data,
    }
}

// For ioctl libcall.
pub const FBIOGET_VSCREENINFO: c_ulong = 0x4600;
pub const FBIOPUT_VSCREENINFO: c_ulong = 0x4601;
pub const FBIOGET_FSCREENINFO: c_ulong = 0x4602;
pub const TCGETS: c_ulong = 0x5401;
pub const TCSETS: c_ulong = 0x5402;
pub const TCSETSW: c_ulong = 0x5403;
pub const TCSETSF: c_ulong = 0x5404;
pub const TCFLSH: c_ulong = 0x540B;
pub const TCSBRK: c_ulong = 0x5409;
pub const TCXONC: c_ulong = 0x540A;

/// https://pubs.opengroup.org/onlinepubs/9799919799/basedefs/termios.h.html
/// these constants should same with termios definition in blueos
pub const TCSANOW: c_int = 0;
pub const TCSADRAIN: c_int = 0x1;
pub const TCSAFLUSH: c_int = 0x2;

pub const TCOOFF: c_int = 0;
pub const TCOON: c_int = 1;
pub const TCIOFF: c_int = 2;
pub const TCION: c_int = 3;

pub const TCIFLUSH: c_int = 0;
pub const TCOFLUSH: c_int = 1;
pub const TCIOFLUSH: c_int = 2;
pub const IGNBRK: c_uint = 0x00000001;
pub const BRKINT: c_uint = 0x00000002;
pub const IGNPAR: c_uint = 0x00000004;
pub const PARMRK: c_uint = 0x00000008;
pub const INPCK: c_uint = 0x00000010;
pub const ISTRIP: c_uint = 0x00000020;
pub const INLCR: c_uint = 0x00000040;
pub const IGNCR: c_uint = 0x00000080;
pub const ICRNL: c_uint = 0x00000100;
pub const IXANY: c_uint = 0x00000800;
pub const IMAXBEL: c_uint = 0x00002000;
pub const IXON: c_uint = 0x00000400;
pub const IXOFF: c_uint = 0x00001000;
pub const ECHO: c_uint = 0x00000008;
pub const ECHOKE: c_uint = 0x00000800;
pub const ECHOE: c_uint = 0x00000010;
pub const ECHOK: c_uint = 0x00000020;
pub const ECHONL: c_uint = 0x00000040;
pub const ECHOPRT: c_uint = 0x00000400;
pub const ECHOCTL: c_uint = 0x00000200;
pub const ISIG: c_uint = 0x00000001;
pub const ICANON: c_uint = 0x00000002;
pub const IEXTEN: c_uint = 0x00008000;
pub const NOFLSH: c_uint = 0x00000080;
pub const TOSTOP: c_uint = 0x00000100;
pub const CSIZE: c_uint = 0x300;
pub const CS6: c_uint = 0x100;
pub const CS7: c_uint = 0x200;
pub const CS8: c_uint = 0x300;
pub const CSTOPB: c_uint = 0x400;
pub const CREAD: c_uint = 0x800;
pub const PARENB: c_uint = 0x1000;
pub const PARODD: c_uint = 0x2000;
pub const HUPCL: c_uint = 0x4000;

pub const B0: c_uint = 0o000000;
pub const B50: c_uint = 0o000001;
pub const B75: c_uint = 0o000002;
pub const B110: c_uint = 0o000003;
pub const B134: c_uint = 0o000004;
pub const B150: c_uint = 0o000005;
pub const B200: c_uint = 0o000006;
pub const B300: c_uint = 0o000007;
pub const B600: c_uint = 0o000010;
pub const B1200: c_uint = 0o000011;
pub const B1800: c_uint = 0o000012;
pub const B2400: c_uint = 0o000013;
pub const B4800: c_uint = 0o000014;
pub const B9600: c_uint = 0o000015;
pub const B19200: c_uint = 0o000016;
pub const B38400: c_uint = 0o000017;
pub const B57600: c_uint = 0o010001;
pub const B115200: c_uint = 0o010002;
pub const B230400: c_uint = 0o010003;
pub const B460800: c_uint = 0o010004;
pub const B500000: c_uint = 0o010005;
pub const B576000: c_uint = 0o010006;
pub const B921600: c_uint = 0o010007;
pub const B1000000: c_uint = 0o010010;
pub const B1152000: c_uint = 0o010011;
pub const B1500000: c_uint = 0o010012;
pub const B2000000: c_uint = 0o010013;
pub const B2500000: c_uint = 0o010014;
pub const B3000000: c_uint = 0o010015;
pub const B3500000: c_uint = 0o010016;
pub const B4000000: c_uint = 0o010017;

pub const OPOST: c_uint = 0x01;
pub const ONLCR: c_uint = 0x04;
pub const OCRNL: c_uint = 0x08;
pub const ONOCR: c_uint = 0x10;
pub const ONLRET: c_uint = 0x20;
pub const OFILL: c_uint = 0x40;
pub const OFDEL: c_uint = 0x80;

pub const VINTR: usize = 0;
pub const VQUIT: usize = 1;
pub const VERASE: usize = 2;
pub const VKILL: usize = 3;
pub const VEOF: usize = 4;
pub const VTIME: usize = 5;
pub const VMIN: usize = 6;
pub const VSWTC: usize = 7;
pub const VSTART: usize = 8;
pub const VSTOP: usize = 9;
pub const VSUSP: usize = 10;
pub const VEOL: usize = 11;

/// https://pubs.opengroup.org/onlinepubs/9799919799/basedefs/sys_socket.h.html
pub const AF_UNIX: c_int = 1;
pub const AF_INET6: c_int = 24;
pub const SOCK_RAW: c_int = 3;
pub const SOCK_RDM: c_int = 4;
pub const SOCK_SEQPACKET: c_int = 5;
pub const SOMAXCONN: c_int = 128;
pub const SO_NONBLOCK: c_int = 0x1100;
pub const IPPROTO_RAW: c_int = 255;
pub const MSG_OOB: c_int = 0x1;
pub const MSG_PEEK: c_int = 0x2;
pub const MSG_DONTROUTE: c_int = 0x4;
pub const MSG_EOR: c_int = 0x8;
pub const MSG_TRUNC: c_int = 0x10;
pub const MSG_CTRUNC: c_int = 0x20;
pub const MSG_WAITALL: c_int = 0x40;
pub const MSG_DONTWAIT: c_int = 0x80;
pub const MSG_BCAST: c_int = 0x100;
pub const MSG_MCAST: c_int = 0x200;

// Refer to FreeBSD.
pub const SOL_SOCKET: c_int = 0xffff;
pub const SO_TYPE: c_int = 0x1008;
pub const SO_PROTOCOL: c_int = 0x1016;
pub const SO_DOMAIN: c_int = 0x1019;

pub const FIONBIO: c_ulong = 1;

// ---- Wireless ioctl constants (linux/wireless.h) ----
pub const SIOCSIWCOMMIT: c_ulong = 0x8B00;
pub const SIOCGIWNAME: c_ulong = 0x8B01;
pub const SIOCSIWNWID: c_ulong = 0x8B02;
pub const SIOCGIWNWID: c_ulong = 0x8B03;
pub const SIOCSIWFREQ: c_ulong = 0x8B04;
pub const SIOCGIWFREQ: c_ulong = 0x8B05;
pub const SIOCSIWMODE: c_ulong = 0x8B06;
pub const SIOCGIWMODE: c_ulong = 0x8B07;
pub const SIOCSIWSENS: c_ulong = 0x8B08;
pub const SIOCGIWSENS: c_ulong = 0x8B09;
pub const SIOCSIWAP: c_ulong = 0x8B14;
pub const SIOCGIWAP: c_ulong = 0x8B15;
pub const SIOCSIWMLME: c_ulong = 0x8B16;
pub const SIOCGIWMLME: c_ulong = 0x8B17;
pub const SIOCSIWSCAN: c_ulong = 0x8B18;
pub const SIOCGIWSCAN: c_ulong = 0x8B19;
pub const SIOCSIWESSID: c_ulong = 0x8B1A;
pub const SIOCGIWESSID: c_ulong = 0x8B1B;
pub const SIOCSIWENCODE: c_ulong = 0x8B2A;
pub const SIOCGIWENCODE: c_ulong = 0x8B2B;
pub const SIOCSIWAUTH: c_ulong = 0x8B32;
pub const SIOCGIWAUTH: c_ulong = 0x8B33;

// Wireless scan flags
pub const IW_SCAN_DEFAULT: c_uint = 0x0000;
pub const IW_SCAN_ALL_ESSID: c_uint = 0x0001;
pub const IW_SCAN_THIS_ESSID: c_uint = 0x0002;
pub const IW_SCAN_ALL_FREQ: c_uint = 0x0004;
pub const IW_SCAN_THIS_FREQ: c_uint = 0x0008;
pub const IW_SCAN_ALL_MODE: c_uint = 0x0010;
pub const IW_SCAN_THIS_MODE: c_uint = 0x0020;
pub const IW_SCAN_ALL_RATE: c_uint = 0x0040;
pub const IW_SCAN_THIS_RATE: c_uint = 0x0080;
pub const IW_SCAN_TYPE_ACTIVE: c_int = 0;
pub const IW_SCAN_TYPE_PASSIVE: c_int = 1;
pub const IW_SCAN_MAX_DATA: usize = 4096;

pub const IW_ESSID_MAX_SIZE: usize = 32;
pub const IW_MAX_FREQUENCIES: usize = 32;

/// https://pubs.opengroup.org/onlinepubs/9799919799/basedefs/poll.h.html
pub const POLLIN: c_short = 0x0001;
pub const POLLPRI: c_short = POLLIN;
pub const POLLOUT: c_short = 0x0004;
pub const POLLRDNORM: c_short = POLLIN;
pub const POLLRDBAND: c_short = POLLIN;
pub const POLLWRNORM: c_short = POLLOUT;
pub const POLLWRBAND: c_short = POLLOUT;
pub const POLLERR: c_short = 0x0008;
pub const POLLHUP: c_short = 0x0010;
pub const POLLNVAL: c_short = 0x0020;

/// https://pubs.opengroup.org/onlinepubs/9799919799/functions/dlsym.html
pub const RTLD_DEFAULT: *mut c_void = 0 as *mut c_void;

/// https://pubs.opengroup.org/onlinepubs/9799919799/basedefs/sys_stat.h.html
pub const UTIME_OMIT: c_long = -1;

/// https://pubs.opengroup.org/onlinepubs/9799919799/basedefs/fcntl.h.html
pub const AT_FDCWD: c_int = -2;
pub const O_DIRECTORY: c_int = 0x200000;
pub const O_NOFOLLOW: c_int = 0x100000;
pub const AT_EACCESS: c_int = 1;
pub const AT_SYMLINK_NOFOLLOW: c_int = 2;
pub const AT_SYMLINK_FOLLOW: c_int = 4;
pub const AT_REMOVEDIR: c_int = 8;

/// https://pubs.opengroup.org/onlinepubs/9799919799/basedefs/signal.h.html
pub const SIGHUP: c_int = 1;
pub const SIGINT: c_int = 2;
pub const SIGQUIT: c_int = 3;
pub const SIGILL: c_int = 4;
pub const SIGTRAP: c_int = 5;
pub const SIGABRT: c_int = 6;
pub const SIGEMT: c_int = 7;
pub const SIGFPE: c_int = 8;
pub const SIGKILL: c_int = 9;
pub const SIGBUS: c_int = 10;
pub const SIGSEGV: c_int = 11;
pub const SIGSYS: c_int = 12;
pub const SIGPIPE: c_int = 13;
pub const SIGALRM: c_int = 14;
pub const SIGTERM: c_int = 15;

/// https://pubs.opengroup.org/onlinepubs/9799919799/basedefs/netdb.h.html
pub const EAI_BADFLAGS: c_int = -1;
pub const EAI_NONAME: c_int = -2;
pub const EAI_AGAIN: c_int = -3;
pub const EAI_FAIL: c_int = -4;
pub const EAI_NODATA: c_int = -5;
pub const EAI_FAMILY: c_int = -6;
pub const EAI_SOCKTYPE: c_int = -7;
pub const EAI_SERVICE: c_int = -8;
pub const EAI_ADDRFAMILY: c_int = -9;
pub const EAI_MEMORY: c_int = -10;
pub const EAI_SYSTEM: c_int = -11;
pub const EAI_OVERFLOW: c_int = -12;

/// https://pubs.opengroup.org/onlinepubs/9799919799/basedefs/limits.h.html
pub const PTHREAD_STACK_MIN: crate::size_t = 4 * 1024;

/// https://pubs.opengroup.org/onlinepubs/9799919799/basedefs/pthread.h.html
pub const PTHREAD_MUTEX_DEFAULT: c_int = crate::PTHREAD_MUTEX_NORMAL;
pub const PTHREAD_MUTEX_STALLED: c_int = 0;
pub const PTHREAD_MUTEX_ROBUST: c_int = 1;
pub const PTHREAD_PRIO_NONE: c_int = 0;
pub const PTHREAD_PROCESS_PRIVATE: c_int = 0;

pub const IP_HDRINCL: c_int = 2;

const _: [(); 0x4600] = [(); FBIOGET_VSCREENINFO as usize];
const _: [(); 0x4601] = [(); FBIOPUT_VSCREENINFO as usize];
const _: [(); 0x4602] = [(); FBIOGET_FSCREENINFO as usize];
const _: [(); 12] = [(); mem::size_of::<fb_bitfield>()];
// BlueOS uses 32-bit `c_ulong` on all targets, so `fb_fix_screeninfo` is
// always 80 bytes regardless of pointer width.
const _: [(); 80] = [(); mem::size_of::<fb_fix_screeninfo>()];
const _: [(); 160] = [(); mem::size_of::<fb_var_screeninfo>()];

extern "C" {
    pub fn futimens(fd: c_int, times: *const timespec) -> c_int;
    pub fn utimensat(
        dirfd: c_int,
        path: *const c_char,
        times: *const timespec,
        flag: c_int,
    ) -> c_int;
    pub fn writev(fd: c_int, iov: *const crate::iovec, iovcnt: c_int) -> crate::ssize_t;
    pub fn readv(fd: c_int, iov: *const crate::iovec, iovcnt: c_int) -> crate::ssize_t;

    pub fn sendmsg(s: c_int, msg: *const crate::msghdr, flags: c_int) -> crate::ssize_t;
    pub fn recvmsg(s: c_int, msg: *mut crate::msghdr, flags: c_int) -> crate::ssize_t;

    pub fn pthread_create(
        native: *mut crate::pthread_t,
        attr: *const crate::pthread_attr_t,
        f: extern "C" fn(_: *mut c_void) -> *mut c_void,
        value: *mut c_void,
    ) -> c_int;

    pub fn pthread_attr_getschedparam(
        attr: *const crate::pthread_attr_t,
        param: *mut sched_param,
    ) -> c_int;

    pub fn pthread_attr_setschedparam(
        attr: *mut crate::pthread_attr_t,
        param: *const sched_param,
    ) -> c_int;

    pub fn pthread_attr_getprocessorid_np(
        attr: *const crate::pthread_attr_t,
        processor_id: *mut c_int,
    ) -> c_int;

    pub fn pthread_attr_setprocessorid_np(
        attr: *mut crate::pthread_attr_t,
        processor_id: c_int,
    ) -> c_int;

    pub fn pthread_getschedparam(
        native: crate::pthread_t,
        policy: *mut c_int,
        param: *mut crate::sched_param,
    ) -> c_int;

    pub fn pthread_setschedparam(
        native: crate::pthread_t,
        policy: c_int,
        param: *const crate::sched_param,
    ) -> c_int;

    pub fn pthread_condattr_getclock(
        attr: *const crate::pthread_condattr_t,
        clock_id: *mut crate::clockid_t,
    ) -> c_int;

    pub fn pthread_condattr_setclock(
        attr: *mut crate::pthread_condattr_t,
        clock_id: crate::clockid_t,
    ) -> c_int;

    pub fn pthread_getprocessorid_np() -> c_int;

    pub fn getentropy(buf: *mut c_void, buflen: crate::size_t) -> c_int;

    pub fn pipe2(fds: *mut c_int, flags: c_int) -> c_int;
}
