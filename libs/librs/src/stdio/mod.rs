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
//
// This code is based on relibc (original license follows):
// https://github.com/redox-os/relibc/blob/master/LICENSE
// standard MIT license

pub use self::constants::*;
use crate::{
    c_str::CStr,
    errno::{SysCallFailed, ERRNO, STR_ERROR},
    fcntl, string,
    sync::GenericMutex,
    syscall::{Sys, Syscall},
    unistd,
};
use alloc::{boxed::Box, vec::Vec};
use blueos_header::syscalls::NR::{Lseek, Rmdir};
use blueos_scal::bk_syscall;
use core::{
    borrow::{Borrow, BorrowMut},
    cmp,
    ffi::VaList as va_list,
    fmt,
    fmt::Write as FmtWrite,
    ops::{Deref, DerefMut},
    ptr, slice, str,
};
use libc::{
    c_char, c_int, c_long, c_ulonglong, c_void, off_t, size_t, EINVAL, FD_CLOEXEC, F_SETFD,
    O_CLOEXEC, O_CREAT, SEEK_CUR, SEEK_SET,
};
mod constants;
pub use self::default::*;
use crate::io::{self, BufRead, BufWriter, LineWriter, Read, Write};
mod default;

pub use self::helpers::*;
mod helpers;
mod lookaheadreader;
use lookaheadreader::LookAheadReader;
mod printf;
mod scanf;
enum Buffer<'a> {
    Borrowed(&'a mut [u8]),
    Owned(Vec<u8>),
}
impl Deref for Buffer<'_> {
    type Target = [u8];

    fn deref(&self) -> &Self::Target {
        match self {
            Buffer::Borrowed(inner) => inner,
            Buffer::Owned(inner) => inner.borrow(),
        }
    }
}
impl DerefMut for Buffer<'_> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        match self {
            Buffer::Borrowed(inner) => inner,
            Buffer::Owned(inner) => inner.borrow_mut(),
        }
    }
}

pub trait Pending {
    fn pending(&self) -> size_t;
}

impl<W: crate::io::Write> Pending for BufWriter<W> {
    fn pending(&self) -> size_t {
        self.buf.len() as size_t
    }
}

impl<W: crate::io::Write> Pending for LineWriter<W> {
    fn pending(&self) -> size_t {
        self.inner.buf.len() as size_t
    }
}

pub trait Writer: io::Write + Pending {
    fn purge(&mut self);
}

impl<W: io::Write> Writer for BufWriter<W> {
    fn purge(&mut self) {
        self.buf.clear();
    }
}
impl<W: io::Write> Writer for LineWriter<W> {
    fn purge(&mut self) {
        self.inner.buf.clear();
    }
}

pub struct FILE {
    lock: GenericMutex<()>,
    file: File,
    flags: c_int,

    read_buf: Buffer<'static>,

    read_pos: usize,
    read_size: usize,
    unget: Vec<u8>,
    writer: Box<dyn Writer + Send>,
    // wchar support
    orientation: c_int,
}

pub struct LockGuard<'a>(&'a mut FILE);
impl Deref for LockGuard<'_> {
    type Target = FILE;

    fn deref(&self) -> &Self::Target {
        self.0
    }
}
impl DerefMut for LockGuard<'_> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.0
    }
}
impl Drop for LockGuard<'_> {
    fn drop(&mut self) {
        unsafe {
            funlockfile(self.0);
        }
    }
}

impl Read for FILE {
    fn read(&mut self, out: &mut [u8]) -> io::Result<usize> {
        let unget_read_size = cmp::min(out.len(), self.unget.len());
        for item in out.iter_mut().take(unget_read_size) {
            *item = self.unget.pop().unwrap();
        }
        if unget_read_size != 0 {
            return Ok(unget_read_size);
        }

        let len = {
            let buf = self.fill_buf()?;
            let len = buf.len().min(out.len());

            out[..len].copy_from_slice(&buf[..len]);
            len
        };
        self.consume(len);
        Ok(len)
    }
}
impl BufRead for FILE {
    fn fill_buf(&mut self) -> io::Result<&[u8]> {
        if self.read_pos == self.read_size {
            self.read_size = match self.file.read(&mut self.read_buf) {
                Ok(0) => {
                    self.flags |= F_EOF;
                    0
                }
                Ok(n) => n,
                Err(err) => {
                    self.flags |= F_ERR;
                    return Err(err);
                }
            };
            self.read_pos = 0;
        }
        Ok(&self.read_buf[self.read_pos..self.read_size])
    }
    fn consume(&mut self, i: usize) {
        self.read_pos = (self.read_pos + i).min(self.read_size);
    }
}
impl Write for FILE {
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        match self.writer.write(buf) {
            Ok(n) => Ok(n),
            Err(err) => {
                self.flags |= F_ERR;
                Err(err)
            }
        }
    }
    fn flush(&mut self) -> io::Result<()> {
        match self.writer.flush() {
            Ok(()) => Ok(()),
            Err(err) => {
                self.flags |= F_ERR;
                Err(err)
            }
        }
    }
}
impl FmtWrite for FILE {
    fn write_str(&mut self, s: &str) -> fmt::Result {
        self.write_all(s.as_bytes())
            .map(|_| ())
            .map_err(|_| fmt::Error)
    }
}

impl WriteByte for FILE {
    fn write_u8(&mut self, c: u8) -> fmt::Result {
        self.write_all(&[c]).map(|_| ()).map_err(|_| fmt::Error)
    }
}
impl FILE {
    pub fn lock(&mut self) -> LockGuard {
        unsafe {
            flockfile(self);
        }
        LockGuard(self)
    }

    pub fn try_set_orientation(&mut self, mode: c_int) -> c_int {
        let stream = self.lock();
        stream.0.try_set_orientation_unlocked(mode)
    }

    pub fn try_set_orientation_unlocked(&mut self, mode: c_int) -> c_int {
        if self.orientation == 0 {
            self.orientation = match mode {
                1..=i32::MAX => 1,
                i32::MIN..=-1 => -1,
                0 => self.orientation,
            };
        }
        self.orientation
    }

    pub fn try_set_byte_orientation_unlocked(&mut self) -> core::result::Result<(), c_int> {
        match self.try_set_orientation_unlocked(-1) {
            i32::MIN..=-1 => Ok(()),
            x => Err(x),
        }
    }

    pub fn try_set_wide_orientation_unlocked(&mut self) -> core::result::Result<(), c_int> {
        match self.try_set_orientation_unlocked(1) {
            1..=i32::MAX => Ok(()),
            x => Err(x),
        }
    }

    pub fn purge(&mut self) {
        // Purge read buffer
        self.read_pos = 0;
        self.read_size = 0;
        // Purge unget
        self.unget.clear();
    }
}

pub unsafe extern "C" fn clearerr(stream: *mut FILE) {
    let mut stream = (*stream).lock();
    stream.flags &= !(F_EOF | F_ERR);
}

#[no_mangle]
pub unsafe extern "C" fn flockfile(file: *mut FILE) {
    (*file).lock.manual_lock();
}

#[no_mangle]
#[linkage = "weak"]
pub unsafe extern "C" fn fclose(stream: *mut FILE) -> c_int {
    let stream = &mut *stream;
    flockfile(stream);

    let mut r = stream.flush().is_err();

    let close = unistd::close(*stream.file) == -1;
    r = r || close;

    if stream.flags & constants::F_PERM == 0 {
        // Not one of stdin, stdout or stderr
        let mut stream = Box::from_raw(stream);
        // Reference files aren't closed on drop, so pretend to be a reference
        stream.file.reference = true;
    } else {
        funlockfile(stream);
    }

    r as c_int
}

#[no_mangle]
pub unsafe extern "C" fn fdopen(fildes: c_int, mode: *const c_char) -> *mut FILE {
    if let Some(f) = helpers::_fdopen(fildes, mode) {
        f
    } else {
        ptr::null_mut()
    }
}

#[no_mangle]
pub unsafe extern "C" fn feof(stream: *mut FILE) -> c_int {
    let stream = (*stream).lock();
    stream.flags & F_EOF
}

#[no_mangle]
pub unsafe extern "C" fn ferror(stream: *mut FILE) -> c_int {
    let stream = (*stream).lock();
    stream.flags & F_ERR
}

#[no_mangle]
#[linkage = "weak"]
pub unsafe extern "C" fn fflush(stream: *mut FILE) -> c_int {
    if stream.is_null() {
        if fflush(stdout) != 0 {
            return EOF;
        }

        if fflush(stderr) != 0 {
            return EOF;
        }
    } else {
        let mut stream = (*stream).lock();
        if stream.flush().is_err() {
            return EOF;
        }
    }

    0
}

#[no_mangle]
pub unsafe extern "C" fn fgetc(stream: *mut FILE) -> c_int {
    let mut stream = (*stream).lock();
    if (*stream).try_set_byte_orientation_unlocked().is_err() {
        return -1;
    }

    getc_unlocked(&mut *stream)
}

#[no_mangle]
pub unsafe extern "C" fn fgets(
    original: *mut c_char,
    max: c_int,
    stream: *mut FILE,
) -> *mut c_char {
    let mut stream = (*stream).lock();
    if (*stream).try_set_byte_orientation_unlocked().is_err() {
        return ptr::null_mut();
    }

    let mut out = original;
    let max = max as usize;
    let mut left = max.saturating_sub(1); // Make space for the terminating NUL-byte
    let mut wrote = false;

    if left >= 1 {
        let unget_read_size = cmp::min(left, stream.unget.len());
        for _ in 0..unget_read_size {
            *out = stream.unget.pop().unwrap() as i8;
            out = out.offset(1);
        }
        left -= unget_read_size;
    }

    loop {
        if left == 0 {
            break;
        }

        let (read, exit) = {
            let buf = match stream.fill_buf() {
                Ok(buf) => buf,
                Err(_) => return ptr::null_mut(),
            };
            if buf.is_empty() {
                break;
            }
            wrote = true;
            let len = buf.len().min(left);

            let newline = buf[..len].iter().position(|&c| c == b'\n');
            let len = newline.map(|i| i + 1).unwrap_or(len);

            ptr::copy_nonoverlapping(buf.as_ptr(), out as *mut u8, len);

            (len, newline.is_some())
        };

        stream.consume(read);

        out = out.add(read);
        left -= read;

        if exit {
            break;
        }
    }

    if max >= 1 {
        // Write the NUL byte
        *out = 0;
    }
    if wrote {
        original
    } else {
        ptr::null_mut()
    }
}

#[no_mangle]
pub unsafe extern "C" fn fileno(stream: *mut FILE) -> c_int {
    let stream = (*stream).lock();
    *stream.file
}

#[no_mangle]
pub unsafe extern "C" fn fopen(filename: *const c_char, mode: *const c_char) -> *mut FILE {
    let initial_mode = *mode;
    if initial_mode != b'r' as i8 && initial_mode != b'w' as i8 && initial_mode != b'a' as i8 {
        ERRNO.set(EINVAL);
        return ptr::null_mut();
    }

    let flags = helpers::parse_mode_flags(mode);

    let new_mode = if flags & O_CREAT == O_CREAT { 0o666 } else { 0 };

    let fd = fcntl::open(filename, flags, new_mode);
    if fd < 0 {
        return ptr::null_mut();
    }

    if flags & O_CLOEXEC > 0 {
        fcntl::fcntl(fd, F_SETFD, FD_CLOEXEC as c_ulonglong);
    }

    if let Some(f) = helpers::_fdopen(fd, mode) {
        f
    } else {
        unistd::close(fd);
        ptr::null_mut()
    }
}

#[no_mangle]
pub unsafe extern "C" fn fputc(c: c_int, stream: *mut FILE) -> c_int {
    let mut stream = (*stream).lock();
    if (*stream).try_set_byte_orientation_unlocked().is_err() {
        return -1;
    }

    putc_unlocked(c, &mut *stream)
}

#[no_mangle]
pub unsafe extern "C" fn fputs(s: *const c_char, stream: *mut FILE) -> c_int {
    let mut stream = (*stream).lock();
    if (*stream).try_set_byte_orientation_unlocked().is_err() {
        return -1;
    }

    let buf = slice::from_raw_parts(s as *mut u8, string::strlen(s));

    if stream.write_all(buf).is_ok() {
        0
    } else {
        -1
    }
}

#[no_mangle]
pub unsafe extern "C" fn fread(
    ptr: *mut c_void,
    size: size_t,
    nitems: size_t,
    stream: *mut FILE,
) -> size_t {
    if size == 0 || nitems == 0 {
        return 0;
    }

    let mut stream = (*stream).lock();
    if (*stream).try_set_byte_orientation_unlocked().is_err() {
        return 0;
    }

    let buf = slice::from_raw_parts_mut(ptr as *mut u8, size * nitems);
    let mut read = 0;
    while read < buf.len() {
        match stream.read(&mut buf[read..]) {
            Ok(0) | Err(_) => break,
            Ok(n) => read += n,
        }
    }
    (read / size) as size_t
}

#[no_mangle]
pub unsafe extern "C" fn fseek(stream: *mut FILE, offset: c_long, whence: c_int) -> c_int {
    fseeko(stream, offset as off_t, whence)
}

#[no_mangle]
pub unsafe extern "C" fn fseeko(stream: *mut FILE, off: off_t, whence: c_int) -> c_int {
    let mut stream = (*stream).lock();
    fseek_locked(&mut stream, off, whence)
}

pub unsafe fn fseek_locked(stream: &mut FILE, mut off: off_t, whence: c_int) -> c_int {
    if whence == SEEK_CUR {
        // Since it's a buffered writer, our actual cursor isn't where the user
        // thinks
        off -= (stream.read_size - stream.read_pos) as off_t;
    }

    // Flush write buffer before seek
    if stream.flush().is_err() {
        return -1;
    }

    let err = bk_syscall!(Lseek, *stream.file, off as usize, whence) as off_t;
    if err < 0 {
        return err as c_int;
    }

    stream.flags &= !(F_EOF | F_ERR);
    stream.read_pos = 0;
    stream.read_size = 0;
    stream.unget = Vec::new();
    0
}

#[no_mangle]
pub unsafe extern "C" fn ftell(stream: *mut FILE) -> c_long {
    ftello(stream) as c_long
}

#[no_mangle]
pub unsafe extern "C" fn ftello(stream: *mut FILE) -> off_t {
    let mut stream = (*stream).lock();
    ftell_locked(&mut stream)
}

pub unsafe extern "C" fn ftell_locked(stream: &mut FILE) -> off_t {
    let pos = bk_syscall!(Lseek, *stream.file, 0, SEEK_CUR) as off_t;
    if pos < 0 {
        return -1;
    }

    pos - (stream.read_size - stream.read_pos) as off_t - stream.unget.len() as off_t
}

#[no_mangle]
pub unsafe extern "C" fn ftrylockfile(file: *mut FILE) -> c_int {
    if (*file).lock.manual_try_lock().is_ok() {
        0
    } else {
        1
    }
}

#[no_mangle]
pub unsafe extern "C" fn funlockfile(file: *mut FILE) {
    (*file).lock.manual_unlock();
}

#[no_mangle]
pub unsafe extern "C" fn fwrite(
    ptr: *const c_void,
    size: size_t,
    nitems: size_t,
    stream: *mut FILE,
) -> size_t {
    if size == 0 || nitems == 0 {
        return 0;
    }
    let mut stream = (*stream).lock();
    if (*stream).try_set_byte_orientation_unlocked().is_err() {
        return 0;
    }

    let buf = slice::from_raw_parts(ptr as *const u8, size * nitems);
    let mut written = 0;
    while written < buf.len() {
        match stream.write(&buf[written..]) {
            Ok(0) | Err(_) => break,
            Ok(n) => written += n,
        }
    }
    (written / size) as size_t
}

#[no_mangle]
pub unsafe extern "C" fn getc(stream: *mut FILE) -> c_int {
    let mut stream = (*stream).lock();
    getc_unlocked(&mut *stream)
}

#[no_mangle]
pub unsafe extern "C" fn getchar() -> c_int {
    fgetc(&mut *stdin)
}

/// Get a char from a stream without locking the stream
#[no_mangle]
pub unsafe extern "C" fn getc_unlocked(stream: *mut FILE) -> c_int {
    if (*stream).try_set_byte_orientation_unlocked().is_err() {
        return -1;
    }

    let mut buf = [0];

    match (*stream).read(&mut buf) {
        Ok(0) | Err(_) => EOF,
        Ok(_) => buf[0] as c_int,
    }
}

#[no_mangle]
pub unsafe extern "C" fn getchar_unlocked() -> c_int {
    getc_unlocked(&mut *stdin)
}

#[no_mangle]
pub unsafe extern "C" fn gets(s: *mut c_char) -> *mut c_char {
    fgets(s, c_int::MAX, &mut *stdin)
}

#[no_mangle]
pub unsafe extern "C" fn perror(s: *const c_char) {
    let err = ERRNO.get();
    let err_str = if err >= 0 && err < STR_ERROR.len() as c_int {
        STR_ERROR[err as usize]
    } else {
        "Unknown error"
    };
    let mut w = FileWriter::new(2);

    // The prefix, `s`, is optional (empty or NULL) according to the spec
    match CStr::from_nullable_ptr(s).and_then(|s_cstr| str::from_utf8(s_cstr.to_bytes()).ok()) {
        Some(s_str) if !s_str.is_empty() => w
            .write_fmt(format_args!("{}: {}\n", s_str, err_str))
            .unwrap(),
        _ => w.write_fmt(format_args!("{}\n", err_str)).unwrap(),
    }
}

#[no_mangle]
pub unsafe extern "C" fn putc(c: c_int, stream: *mut FILE) -> c_int {
    let mut stream = (*stream).lock();
    putc_unlocked(c, &mut *stream)
}

#[no_mangle]
pub unsafe extern "C" fn putchar(c: c_int) -> c_int {
    fputc(c, &mut *stdout)
}

#[no_mangle]
pub unsafe extern "C" fn putc_unlocked(c: c_int, stream: *mut FILE) -> c_int {
    if (*stream).try_set_byte_orientation_unlocked().is_err() {
        return -1;
    }

    match (*stream).write(&[c as u8]) {
        Ok(0) | Err(_) => EOF,
        Ok(_) => c,
    }
}

#[no_mangle]
pub unsafe extern "C" fn puts(s: *const c_char) -> c_int {
    let mut stream = (*stdout).lock();
    if (*stream).try_set_byte_orientation_unlocked().is_err() {
        return -1;
    }

    let buf = slice::from_raw_parts(s as *mut u8, string::strlen(s));

    if stream.write_all(buf).is_err() {
        return -1;
    }
    if stream.write(b"\n").is_err() {
        return -1;
    }
    0
}

#[no_mangle]
pub unsafe extern "C" fn rmdir(path: *const c_char) -> c_int {
    let path = CStr::from_ptr(path);
    Sys::rmdir(path).map(|_| 0).syscall_failed()
}

#[no_mangle]
pub unsafe extern "C" fn rewind(stream: *mut FILE) {
    fseeko(stream, 0, SEEK_SET);
}

#[no_mangle]
pub unsafe extern "C" fn setbuf(stream: *mut FILE, buf: *mut c_char) {
    setvbuf(
        stream,
        buf,
        if buf.is_null() { _IONBF } else { _IOFBF },
        BUFSIZ as usize,
    );
}

#[no_mangle]
pub unsafe extern "C" fn setvbuf(
    stream: *mut FILE,
    buf: *mut c_char,
    _mode: c_int,
    mut size: size_t,
) -> c_int {
    let mut stream = (*stream).lock();
    // Set a buffer of size `size` if no buffer is given
    stream.read_buf = if buf.is_null() || size == 0 {
        if size == 0 {
            size = BUFSIZ as usize;
        }
        Buffer::Owned(vec![0; size])
    } else {
        Buffer::Borrowed(slice::from_raw_parts_mut(buf as *mut u8, size))
    };
    stream.flags |= F_SVB;
    0
}

#[no_mangle]
pub unsafe extern "C" fn ungetc(c: c_int, stream: *mut FILE) -> c_int {
    let mut stream = (*stream).lock();
    if (*stream).try_set_byte_orientation_unlocked().is_err() {
        return -1;
    }

    stream.unget.push(c as u8);
    c
}

#[no_mangle]
pub unsafe extern "C" fn vfprintf(file: *mut FILE, format: *const c_char, ap: va_list) -> c_int {
    let mut file = (*file).lock();
    if file.try_set_byte_orientation_unlocked().is_err() {
        return -1;
    }

    printf::printf(&mut *file, format, ap)
}

#[no_mangle]
pub unsafe extern "C" fn fprintf(
    file: *mut FILE,
    format: *const c_char,
    mut __valist: ...
) -> c_int {
    vfprintf(file, format, __valist.as_va_list())
}

#[no_mangle]
pub unsafe extern "C" fn vprintf(format: *const c_char, ap: va_list) -> c_int {
    vfprintf(&mut *stdout, format, ap)
}

#[no_mangle]
pub unsafe extern "C" fn printf(format: *const c_char, mut __valist: ...) -> c_int {
    vfprintf(&mut *stdout, format, __valist.as_va_list())
}

#[no_mangle]
pub unsafe extern "C" fn vsnprintf(
    s: *mut c_char,
    n: size_t,
    format: *const c_char,
    ap: va_list,
) -> c_int {
    printf::printf(&mut StringWriter(s as *mut u8, n), format, ap)
}

#[no_mangle]
pub unsafe extern "C" fn snprintf(
    s: *mut c_char,
    n: size_t,
    format: *const c_char,
    mut __valist: ...
) -> c_int {
    printf::printf(
        &mut StringWriter(s as *mut u8, n),
        format,
        __valist.as_va_list(),
    )
}

#[no_mangle]
pub unsafe extern "C" fn vsprintf(s: *mut c_char, format: *const c_char, ap: va_list) -> c_int {
    printf::printf(&mut UnsafeStringWriter(s as *mut u8), format, ap)
}
#[no_mangle]
pub unsafe extern "C" fn sprintf(
    s: *mut c_char,
    format: *const c_char,
    mut __valist: ...
) -> c_int {
    printf::printf(
        &mut UnsafeStringWriter(s as *mut u8),
        format,
        __valist.as_va_list(),
    )
}

#[no_mangle]
pub unsafe extern "C" fn vfscanf(file: *mut FILE, format: *const c_char, ap: va_list) -> c_int {
    let ret = {
        let mut file = (*file).lock();
        if file.try_set_byte_orientation_unlocked().is_err() {
            return -1;
        }

        let f: &mut FILE = &mut file;
        let reader: LookAheadReader = f.into();
        scanf::scanf(reader, format, ap)
    };
    ret
}

#[no_mangle]
pub unsafe extern "C" fn fscanf(
    file: *mut FILE,
    format: *const c_char,
    mut __valist: ...
) -> c_int {
    vfscanf(file, format, __valist.as_va_list())
}

#[no_mangle]
pub unsafe extern "C" fn vscanf(format: *const c_char, ap: va_list) -> c_int {
    vfscanf(&mut *stdin, format, ap)
}
#[no_mangle]
pub unsafe extern "C" fn scanf(format: *const c_char, mut __valist: ...) -> c_int {
    vfscanf(&mut *stdin, format, __valist.as_va_list())
}

#[no_mangle]
pub unsafe extern "C" fn vsscanf(s: *const c_char, format: *const c_char, ap: va_list) -> c_int {
    let reader = (s as *const u8).into();
    scanf::scanf(reader, format, ap)
}
#[no_mangle]
pub unsafe extern "C" fn sscanf(
    s: *const c_char,
    format: *const c_char,
    mut __valist: ...
) -> c_int {
    let reader = (s as *const u8).into();
    scanf::scanf(reader, format, __valist.as_va_list())
}

pub fn init() {
    unsafe {
        // Initialize stdin/stdout/stderr.
        // TODO: const fn initialization of FILE
        stdin = default_stdin().get();
        stdout = default_stdout().get();
        stderr = default_stderr().get();
    }
}
