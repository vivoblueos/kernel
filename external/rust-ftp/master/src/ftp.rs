//! FTP module.

use super::{
    data_stream::DataStream,
    status,
    types::{FileType, FtpError, Line},
};

#[cfg(not(target_os = "blueos"))]
use {
    chrono::{offset::TimeZone, DateTime, Utc},
    regex::Regex,
};

use std::{
    borrow::Cow,
    io::{copy, BufRead, BufReader, BufWriter, Cursor, Read, Write},
    net::{SocketAddr, TcpStream, ToSocketAddrs},
    str::FromStr,
};

#[cfg(all(feature = "secure", feature = "native-tls"))]
use native_tls::TlsConnector;
#[cfg(all(feature = "secure", not(feature = "native-tls")))]
use openssl::ssl::{Ssl, SslContext};

#[cfg(not(target_os = "blueos"))]
lazy_static! {
    // This regex extracts IP and Port details from PASV command response.
    // The regex looks for the pattern (h1,h2,h3,h4,p1,p2).
    static ref PORT_RE: Regex = Regex::new(r"\((\d+),(\d+),(\d+),(\d+),(\d+),(\d+)\)").unwrap();

    // This regex extracts modification time from MDTM command response.
    static ref MDTM_RE: Regex = Regex::new(r"\b(\d{4})(\d{2})(\d{2})(\d{2})(\d{2})(\d{2})\b").unwrap();

    // This regex extracts file size from SIZE command response.
    static ref SIZE_RE: Regex = Regex::new(r"\s+(\d+)\s*$").unwrap();
}

/// Stream to interface with the FTP server. This interface is only for the command stream.
#[derive(Debug)]
pub struct FtpStream {
    reader: BufReader<DataStream>,
    welcome_msg: Option<String>,
    #[cfg(all(feature = "secure", feature = "native-tls"))]
    tls_ctx: Option<TlsConnector>,
    #[cfg(all(feature = "secure", feature = "native-tls"))]
    domain: Option<String>,
    #[cfg(all(feature = "secure", not(feature = "native-tls")))]
    ssl_cfg: Option<SslContext>,
}

impl FtpStream {
    /// Creates an FTP Stream and returns the welcome message
    #[cfg(not(feature = "secure"))]
    pub fn connect<A: ToSocketAddrs>(addr: A) -> crate::Result<FtpStream> {
        TcpStream::connect(addr)
            .map_err(FtpError::ConnectionError)
            .and_then(|stream| {
                let mut ftp_stream = FtpStream {
                    reader: BufReader::new(DataStream::Tcp(stream)),
                    welcome_msg: None,
                };

                match ftp_stream.read_response(status::READY) {
                    Ok(response) => {
                        ftp_stream.welcome_msg = Some(response.1);
                        Ok(ftp_stream)
                    }
                    Err(err) => Err(err),
                }
            })
    }

    /// Creates an FTP Stream and returns the welcome message
    #[cfg(all(feature = "secure", feature = "native-tls"))]
    pub fn connect<A: ToSocketAddrs>(addr: A) -> crate::Result<FtpStream> {
        TcpStream::connect(addr)
            .map_err(FtpError::ConnectionError)
            .and_then(|stream| {
                let mut ftp_stream = FtpStream {
                    reader: BufReader::new(DataStream::Tcp(stream)),
                    tls_ctx: None,
                    domain: None,
                    welcome_msg: None,
                };

                match ftp_stream.read_response(status::READY) {
                    Ok(response) => {
                        ftp_stream.welcome_msg = Some(response.1);
                        Ok(ftp_stream)
                    }
                    Err(err) => Err(err),
                }
            })
    }

    /// Creates an FTP Stream and returns the welcome message
    #[cfg(all(feature = "secure", not(feature = "native-tls")))]
    pub fn connect<A: ToSocketAddrs>(addr: A) -> crate::Result<FtpStream> {
        TcpStream::connect(addr)
            .map_err(FtpError::ConnectionError)
            .and_then(|stream| {
                let mut ftp_stream = FtpStream {
                    reader: BufReader::new(DataStream::Tcp(stream)),
                    ssl_cfg: None,
                    welcome_msg: None,
                };

                match ftp_stream.read_response(status::READY) {
                    Ok(response) => {
                        ftp_stream.welcome_msg = Some(response.1);
                        Ok(ftp_stream)
                    }
                    Err(err) => Err(err),
                }
            })
    }

    /// Switch to a secure mode if possible, using a provided SSL configuration.
    /// This method does nothing if the connect is already secured.
    ///
    /// ## Panics
    ///
    /// Panics if the plain TCP connection cannot be switched to TLS mode.
    ///
    /// ## Example
    ///
    /// ```rust,no_run
    /// use std::path::Path;
    /// use ftp::FtpStream;
    /// use ftp::native_tls::{TlsConnector, TlsStream};
    ///
    /// // Create a TlsConnector
    /// // NOTE: For custom options see <https://docs.rs/native-tls/0.2.6/native_tls/struct.TlsConnectorBuilder.html>
    /// let mut ctx = TlsConnector::new().unwrap();
    /// let mut (ftp_stream, _welcome_msg) = FtpStream::connect("127.0.0.1:21").unwrap();
    /// let mut ftp_stream = ftp_stream.into_secure(ctx, "localhost").unwrap();
    /// ```
    #[cfg(all(feature = "secure", feature = "native-tls"))]
    pub fn into_secure(
        mut self,
        tls_connector: TlsConnector,
        domain: &str,
    ) -> crate::Result<FtpStream> {
        // Ask the server to start securing data.
        self.write_str("AUTH TLS\r\n")?;
        self.read_response(status::AUTH_OK)?;

        let mut secured_ftp_tream = FtpStream {
            reader: BufReader::new(DataStream::Ssl(
                tls_connector.connect(domain, self.reader.into_inner().into_tcp_stream())?,
            )),
            tls_ctx: Some(tls_connector),
            domain: Some(String::from(domain)),
        };
        // Set protection buffer size
        secured_ftp_tream.write_str("PBSZ 0\r\n")?;
        secured_ftp_tream.read_response(status::COMMAND_OK)?;
        // Change the level of data protectio to Private
        secured_ftp_tream.write_str("PROT P\r\n")?;
        secured_ftp_tream.read_response(status::COMMAND_OK)?;

        Ok(secured_ftp_tream)
    }

    /// Switch to insecure mode. If the connection is already
    /// insecure does nothing.
    ///
    /// ## Example
    ///
    /// ```rust,no_run
    /// use std::path::Path;
    /// use ftp::FtpStream;
    ///
    /// use ftp::native_tls::{TlsConnector, TlsStream};
    ///
    /// // Create an TlsConnector
    /// let mut ctx = TlsConnector::new().unwrap();
    /// let mut (ftp_stream, _welcome_msg) = FtpStream::connect("127.0.0.1:21").unwrap();
    /// let mut ftp_stream = ftp_stream.into_secure(ctx, "localhost").unwrap();
    /// // Do all secret things
    /// // Switch back to the insecure mode
    /// let mut ftp_stream = ftp_stream.into_insecure().unwrap();
    /// // Do all public things
    /// let _ = ftp_stream.quit();
    /// ```
    #[cfg(all(feature = "secure", feature = "native-tls"))]
    pub fn into_insecure(mut self) -> crate::Result<FtpStream> {
        // Ask the server to stop securing data
        self.write_str("CCC\r\n")?;
        self.read_response(status::COMMAND_OK)?;
        let plain_ftp_stream = FtpStream {
            reader: BufReader::new(DataStream::Tcp(self.reader.into_inner().into_tcp_stream())),
            tls_ctx: None,
            domain: None,
        };
        Ok(plain_ftp_stream)
    }

    /// Switch to a secure mode if possible, using a provided SSL configuration.
    /// This method does nothing if the connect is already secured.
    ///
    /// ## Panics
    ///
    /// Panics if the plain TCP connection cannot be switched to TLS mode.
    ///
    /// ## Example
    ///
    /// ```rust,no_run
    /// use std::path::Path;
    /// use ftp::FtpStream;
    /// use ftp::openssl::ssl::{ SslContext, SslMethod };
    ///
    /// // Create an SslContext with a custom cert.
    /// let mut ctx = SslContext::builder(SslMethod::tls()).unwrap();
    /// let _ = ctx.set_ca_file(Path::new("/path/to/a/cert.pem")).unwrap();
    /// let ctx = ctx.build();
    /// let mut ftp_stream = FtpStream::connect("127.0.0.1:21").unwrap();
    /// let mut ftp_stream = ftp_stream.into_secure(ctx).unwrap();
    /// ```
    #[cfg(all(feature = "secure", not(feature = "native-tls")))]
    pub fn into_secure(mut self, ssl_context: SslContext) -> crate::Result<FtpStream> {
        // Ask the server to start securing data.
        self.write_str("AUTH TLS\r\n")?;
        self.read_response(status::AUTH_OK)?;

        let mut secured_ftp_tream = FtpStream {
            reader: BufReader::new(DataStream::Ssl(
                Ssl::new(&ssl_context)?
                    .connect(self.reader.into_inner().into_tcp_stream())
                    .map_err(|e| FtpError::SecureError(e.to_string()))?,
            )),
            ssl_cfg: Some(ssl_context),
            welcome_msg: self.welcome_msg,
        };
        // Set protection buffer size
        secured_ftp_tream.write_str("PBSZ 0\r\n")?;
        secured_ftp_tream.read_response(status::COMMAND_OK)?;
        // Change the level of data protectio to Private
        secured_ftp_tream.write_str("PROT P\r\n")?;
        secured_ftp_tream.read_response(status::COMMAND_OK)?;

        Ok(secured_ftp_tream)
    }

    /// Switch to insecure mode.
    ///
    /// ## Example
    ///
    /// ```rust,no_run
    /// use std::path::Path;
    /// use ftp::FtpStream;
    ///
    /// use ftp::openssl::ssl::{ SslContext, SslMethod };
    ///
    /// // Create an SslContext with a custom cert.
    /// let mut ctx = SslContext::builder(SslMethod::tls()).unwrap();
    /// let _ = ctx.set_ca_file(Path::new("/path/to/a/cert.pem")).unwrap();
    /// let ctx = ctx.build();
    /// let mut ftp_stream = FtpStream::connect("127.0.0.1:21").unwrap();
    /// let mut ftp_stream = ftp_stream.into_secure(ctx).unwrap();
    /// // Do all secret things
    /// // Switch back to the insecure mode
    /// let mut ftp_stream = ftp_stream.into_insecure().unwrap();
    /// // Do all public things
    /// let _ = ftp_stream.quit();
    /// ```
    #[cfg(all(feature = "secure", not(feature = "native-tls")))]
    pub fn into_insecure(mut self) -> crate::Result<FtpStream> {
        // Ask the server to stop securing data
        self.write_str("CCC\r\n")?;
        self.read_response(status::COMMAND_OK)?;

        let plain_ftp_stream = FtpStream {
            reader: BufReader::new(DataStream::Tcp(self.reader.into_inner().into_tcp_stream())),
            ssl_cfg: None,
            welcome_msg: self.welcome_msg,
        };

        Ok(plain_ftp_stream)
    }

    /// Execute command which send data back in a separate stream
    #[cfg(not(feature = "secure"))]
    fn data_command(&mut self, cmd: &str) -> crate::Result<DataStream> {
        let addr = self.pasv()?;
        self.write_str(cmd)?;
        Ok(DataStream::Tcp(TcpStream::connect(addr)?))
    }

    /// Execute command which send data back in a separate stream
    #[cfg(all(feature = "secure", feature = "native-tls"))]
    fn data_command(&mut self, cmd: &str) -> crate::Result<DataStream> {
        let addr = self.pasv()?;
        self.write_str(cmd)?;
        let stream = TcpStream::connect(addr)?;

        Ok(match self.tls_ctx {
            Some(ref tls_ctx) => {
                DataStream::Ssl(tls_ctx.connect(self.domain.as_ref().unwrap(), stream)?)
            }
            None => DataStream::Tcp(stream),
        })
    }

    /// Execute command which send data back in a separate stream
    #[cfg(all(feature = "secure", not(feature = "native-tls")))]
    fn data_command(&mut self, cmd: &str) -> crate::Result<DataStream> {
        let addr = self.pasv()?;
        self.write_str(cmd)?;
        let stream = TcpStream::connect(addr)?;

        Ok(match self.ssl_cfg {
            Some(ref ssl_cfg) => {
                let mut ssl = Ssl::new(ssl_cfg)?;
                if let DataStream::Ssl(ssl_stream) = self.reader.get_ref() {
                    unsafe {
                        // SAFETY: ssl_stream was also using the context from self.ssl_cfg
                        ssl.set_session(ssl_stream.ssl().session().unwrap())?
                    }
                };
                DataStream::Ssl(ssl.connect(stream)?)
            }
            None => DataStream::Tcp(stream),
        })
    }

    /// Returns a reference to the underlying TcpStream.
    ///
    /// Example:
    /// ```no_run
    /// use std::net::TcpStream;
    /// use ftp::FtpStream;
    /// use std::time::Duration;
    ///
    /// let stream = FtpStream::connect("127.0.0.1:21")
    ///                        .expect("Couldn't connect to the server...");
    /// stream.get_ref().set_read_timeout(Some(Duration::from_secs(10)))
    ///                 .expect("set_read_timeout call failed");
    /// ```
    pub fn get_ref(&self) -> &TcpStream {
        self.reader.get_ref().get_ref()
    }

    /// Get welcome message from the server on connect.
    pub fn get_welcome_msg(&self) -> Option<&str> {
        self.welcome_msg.as_deref()
    }

    /// Log in to the FTP server.
    pub fn login(&mut self, user: &str, password: &str) -> crate::Result<()> {
        self.write_str(format!("USER {}\r\n", user))?;
        let Line(code, _) = self.read_response_in(&[status::LOGGED_IN, status::NEED_PASSWORD])?;
        if code == status::NEED_PASSWORD {
            self.write_str(format!("PASS {}\r\n", password))?;
            self.read_response(status::LOGGED_IN)?;
        }
        Ok(())
    }

    /// Change the current directory to the path specified.
    pub fn cwd(&mut self, path: &str) -> crate::Result<()> {
        self.write_str(format!("CWD {}\r\n", path))?;
        self.read_response(status::REQUESTED_FILE_ACTION_OK)?;
        Ok(())
    }

    /// Move the current directory to the parent directory.
    pub fn cdup(&mut self) -> crate::Result<()> {
        self.write_str("CDUP\r\n")?;
        self.read_response_in(&[status::COMMAND_OK, status::REQUESTED_FILE_ACTION_OK])?;
        Ok(())
    }

    /// Gets the current directory
    pub fn pwd(&mut self) -> crate::Result<String> {
        self.write_str("PWD\r\n")?;
        let Line(_, content) = self.read_response(status::PATH_CREATED)?;
        match (content.find('"'), content.rfind('"')) {
            (Some(begin), Some(end)) if begin < end => Ok(content[begin + 1..end].to_string()),
            _ => {
                let cause = format!("Invalid PWD Response: {}", content);
                Err(FtpError::InvalidResponse(cause))
            }
        }
    }

    /// This does nothing. This is usually just used to keep the connection open.
    pub fn noop(&mut self) -> crate::Result<()> {
        self.write_str("NOOP\r\n")?;
        self.read_response(status::COMMAND_OK).map(|_| ())
    }

    /// This creates a new directory on the server.
    pub fn mkdir(&mut self, pathname: &str) -> crate::Result<()> {
        self.write_str(format!("MKD {}\r\n", pathname))?;
        self.read_response(status::PATH_CREATED).map(|_| ())
    }

    /// Runs the PASV command.
    #[cfg(not(target_os = "blueos"))]
    fn pasv(&mut self) -> crate::Result<SocketAddr> {
        self.write_str("PASV\r\n")?;
        // PASV response format : 227 Entering Passive Mode (h1,h2,h3,h4,p1,p2).
        let Line(_, line) = self.read_response(status::PASSIVE_MODE)?;
        PORT_RE
            .captures(&line)
            .ok_or_else(|| FtpError::InvalidResponse(format!("Invalid PASV response: {}", line)))
            .and_then(|caps| {
                // If the regex matches we can be sure groups contains numbers
                let (oct1, oct2, oct3, oct4) = (
                    caps[1].parse::<u8>().unwrap(),
                    caps[2].parse::<u8>().unwrap(),
                    caps[3].parse::<u8>().unwrap(),
                    caps[4].parse::<u8>().unwrap(),
                );
                let (msb, lsb) = (
                    caps[5].parse::<u8>().unwrap(),
                    caps[6].parse::<u8>().unwrap(),
                );
                let port = ((msb as u16) << 8) + lsb as u16;
                let addr = format!("{}.{}.{}.{}:{}", oct1, oct2, oct3, oct4, port);
                SocketAddr::from_str(&addr).map_err(FtpError::InvalidAddress)
            })
    }

    /// Runs the PASV command.
    #[cfg(target_os = "blueos")]
    fn pasv(&mut self) -> crate::Result<SocketAddr> {
        self.write_str("PASV\r\n")?;
        // PASV response format : 227 Entering Passive Mode (h1,h2,h3,h4,p1,p2).
        let Line(_, line) = self.read_response(status::PASSIVE_MODE)?;

        let start = line
            .find('(')
            .ok_or_else(|| FtpError::InvalidResponse(format!("Invalid PASV response: {}", line)))?;
        let end = line
            .find(')')
            .ok_or_else(|| FtpError::InvalidResponse(format!("Invalid PASV response: {}", line)))?;
        let parts: Vec<&str> = line[start + 1..end].split(',').collect();

        if parts.len() != 6 {
            return Err(FtpError::InvalidResponse(format!(
                "Invalid PASV response: {}",
                line
            )));
        }

        let ip = format!("{}.{}.{}.{}", parts[0], parts[1], parts[2], parts[3]);
        let p1: u16 = parts[4]
            .parse()
            .map_err(|_| FtpError::InvalidResponse(format!("Invalid PASV response: {}", line)))?;
        let p2: u16 = parts[5]
            .parse()
            .map_err(|_| FtpError::InvalidResponse(format!("Invalid PASV response: {}", line)))?;

        let addr_str = format!("{}:{}", ip, p1 * 256 + p2);
        SocketAddr::from_str(&addr_str).map_err(FtpError::InvalidAddress)
    }

    /// Sets the type of file to be transferred. That is the implementation
    /// of `TYPE` command.
    pub fn transfer_type(&mut self, file_type: FileType) -> crate::Result<()> {
        let type_command = format!("TYPE {}\r\n", file_type.to_string());
        self.write_str(&type_command)?;
        self.read_response(status::COMMAND_OK).map(|_| ())
    }

    /// Quits the current FTP session.
    pub fn quit(&mut self) -> crate::Result<()> {
        self.write_str("QUIT\r\n")?;
        self.read_response(status::CLOSING).map(|_| ())
    }

    /// Retrieves the file name specified from the server.
    /// This method is a more complicated way to retrieve a file.
    /// The reader returned should be dropped.
    /// Also you will have to read the response to make sure it has the correct value.
    pub fn get(&mut self, file_name: &str) -> crate::Result<BufReader<DataStream>> {
        let retr_command = format!("RETR {}\r\n", file_name);
        let data_stream = BufReader::new(self.data_command(&retr_command)?);
        self.read_response_in(&[status::ABOUT_TO_SEND, status::ALREADY_OPEN])?;
        Ok(data_stream)
    }

    /// Renames the file from_name to to_name
    pub fn rename(&mut self, from_name: &str, to_name: &str) -> crate::Result<()> {
        self.write_str(format!("RNFR {}\r\n", from_name))?;
        self.read_response(status::REQUEST_FILE_PENDING)
            .and_then(|_| {
                self.write_str(format!("RNTO {}\r\n", to_name))?;
                self.read_response(status::REQUESTED_FILE_ACTION_OK)
                    .map(|_| ())
            })
    }

    /// The implementation of `RETR` command where `filename` is the name of the file
    /// to download from FTP and `reader` is the function which operates with the
    /// data stream opened.
    ///
    /// ```
    /// # use ftp::{FtpStream, FtpError};
    /// # use std::io::Cursor;
    /// # let mut conn = FtpStream::connect("127.0.0.1:21").unwrap();
    /// # conn.login("Doe", "mumble").and_then(|_| {
    /// #     let mut reader = Cursor::new("hello, world!".as_bytes());
    /// #     conn.put("retr.txt", &mut reader)
    /// # }).unwrap();
    /// assert!(conn.retr("retr.txt", |stream| {
    ///     let mut buf = Vec::new();
    ///     stream.read_to_end(&mut buf).map(|_|
    ///         assert_eq!(buf, "hello, world!".as_bytes())
    ///     ).map_err(|e| FtpError::ConnectionError(e))
    /// }).is_ok());
    /// # assert!(conn.rm("retr.txt").is_ok());
    /// ```
    pub fn retr<F, T>(&mut self, filename: &str, reader: F) -> crate::Result<T>
    where
        F: Fn(&mut dyn Read) -> crate::Result<T>,
    {
        let retr_command = format!("RETR {}\r\n", filename);
        {
            let mut data_stream = BufReader::new(self.data_command(&retr_command)?);
            self.read_response_in(&[status::ABOUT_TO_SEND, status::ALREADY_OPEN])
                .and_then(|_| reader(&mut data_stream))
        }
        .and_then(|res| {
            self.read_response_in(&[
                status::CLOSING_DATA_CONNECTION,
                status::REQUESTED_FILE_ACTION_OK,
            ])
            .map(|_| res)
        })
    }

    /// Simple way to retr a file from the server. This stores the file in memory.
    ///
    /// ```
    /// # use ftp::{FtpStream, FtpError};
    /// # use std::io::Cursor;
    /// # let mut conn = FtpStream::connect("127.0.0.1:21").unwrap();
    /// # conn.login("Doe", "mumble").and_then(|_| {
    /// #     let mut reader = Cursor::new("hello, world!".as_bytes());
    /// #     conn.put("simple_retr.txt", &mut reader)
    /// # }).unwrap();
    /// let cursor = conn.simple_retr("simple_retr.txt").unwrap();
    /// // do something with bytes
    /// assert_eq!(cursor.into_inner(), "hello, world!".as_bytes());
    /// # assert!(conn.rm("simple_retr.txt").is_ok());
    /// ```
    pub fn simple_retr(&mut self, file_name: &str) -> crate::Result<Cursor<Vec<u8>>> {
        self.retr(file_name, |reader| {
            let mut buffer = Vec::new();
            reader
                .read_to_end(&mut buffer)
                .map(|_| buffer)
                .map_err(FtpError::ConnectionError)
        })
        .map(Cursor::new)
    }

    /// Removes the remote pathname from the server.
    pub fn rmdir(&mut self, pathname: &str) -> crate::Result<()> {
        self.write_str(format!("RMD {}\r\n", pathname))?;
        self.read_response(status::REQUESTED_FILE_ACTION_OK)
            .map(|_| ())
    }

    /// Remove the remote file from the server.
    pub fn rm(&mut self, filename: &str) -> crate::Result<()> {
        self.write_str(format!("DELE {}\r\n", filename))?;
        self.read_response(status::REQUESTED_FILE_ACTION_OK)
            .map(|_| ())
    }

    fn put_file<R: Read>(&mut self, filename: &str, r: &mut R) -> crate::Result<()> {
        let stor_command = format!("STOR {}\r\n", filename);
        let mut data_stream = BufWriter::new(self.data_command(&stor_command)?);
        self.read_response_in(&[status::ALREADY_OPEN, status::ABOUT_TO_SEND])?;
        copy(r, &mut data_stream)?;
        #[cfg(all(feature = "secure", not(feature = "native-tls")))]
        {
            if let DataStream::Ssl(mut ssl_stream) =
                data_stream.into_inner().map_err(std::io::Error::from)?
            {
                ssl_stream.shutdown()?;
            }
        }
        Ok(())
    }

    /// This stores a file on the server.
    pub fn put<R: Read>(&mut self, filename: &str, r: &mut R) -> crate::Result<()> {
        self.put_file(filename, r)?;
        self.read_response_in(&[
            status::CLOSING_DATA_CONNECTION,
            status::REQUESTED_FILE_ACTION_OK,
        ])
        .map(|_| ())
    }

    /// Execute a command which returns list of strings in a separate stream
    fn list_command(
        &mut self,
        cmd: Cow<'static, str>,
        open_code: u32,
        close_code: &[u32],
    ) -> crate::Result<Vec<String>> {
        let data_stream = BufReader::new(self.data_command(&cmd)?);
        self.read_response_in(&[open_code, status::ALREADY_OPEN])?;
        let lines = Self::get_lines_from_stream(data_stream);
        self.read_response_in(close_code)?;
        lines
    }

    fn get_lines_from_stream(data_stream: BufReader<DataStream>) -> crate::Result<Vec<String>> {
        let mut lines: Vec<String> = Vec::new();

        let mut lines_stream = data_stream.lines();
        loop {
            let line = lines_stream.next();
            match line {
                Some(line) => match line {
                    Ok(l) => {
                        if l.is_empty() {
                            continue;
                        }
                        lines.push(l);
                    }
                    Err(_) => {
                        return Err(FtpError::InvalidResponse(String::from(
                            "Invalid lines in response",
                        )))
                    }
                },
                None => break Ok(lines),
            }
        }
    }

    /// Execute `LIST` command which returns the detailed file listing in human readable format.
    /// If `pathname` is omited then the list of files in the current directory will be
    /// returned otherwise it will the list of files on `pathname`.
    pub fn list(&mut self, pathname: Option<&str>) -> crate::Result<Vec<String>> {
        let command = pathname.map_or("LIST\r\n".into(), |path| {
            format!("LIST {}\r\n", path).into()
        });

        self.list_command(
            command,
            status::ABOUT_TO_SEND,
            &[
                status::CLOSING_DATA_CONNECTION,
                status::REQUESTED_FILE_ACTION_OK,
            ],
        )
    }

    /// Execute `NLST` command which returns the list of file names only.
    /// If `pathname` is omited then the list of files in the current directory will be
    /// returned otherwise it will the list of files on `pathname`.
    pub fn nlst(&mut self, pathname: Option<&str>) -> crate::Result<Vec<String>> {
        let command = pathname.map_or("NLST\r\n".into(), |path| {
            format!("NLST {}\r\n", path).into()
        });

        self.list_command(
            command,
            status::ABOUT_TO_SEND,
            &[
                status::CLOSING_DATA_CONNECTION,
                status::REQUESTED_FILE_ACTION_OK,
            ],
        )
    }

    /// Retrieves the modification time of the file at `pathname` if it exists.
    /// In case the file does not exist `None` is returned.
    #[cfg(not(target_os = "blueos"))]
    pub fn mdtm(&mut self, pathname: &str) -> crate::Result<Option<DateTime<Utc>>> {
        self.write_str(format!("MDTM {}\r\n", pathname))?;
        let Line(_, content) = self.read_response(status::FILE)?;

        match MDTM_RE.captures(&content) {
            Some(caps) => {
                let (year, month, day) = (
                    caps[1].parse::<i32>().unwrap(),
                    caps[2].parse::<u32>().unwrap(),
                    caps[3].parse::<u32>().unwrap(),
                );
                let (hour, minute, second) = (
                    caps[4].parse::<u32>().unwrap(),
                    caps[5].parse::<u32>().unwrap(),
                    caps[6].parse::<u32>().unwrap(),
                );
                Ok(Some(
                    Utc.ymd(year, month, day).and_hms(hour, minute, second),
                ))
            }
            None => Ok(None),
        }
    }

    /// Retrieves the size of the file in bytes at `pathname` if it exists.
    /// In case the file does not exist `None` is returned.
    #[cfg(not(target_os = "blueos"))]
    pub fn size(&mut self, pathname: &str) -> crate::Result<Option<usize>> {
        self.write_str(format!("SIZE {}\r\n", pathname))?;
        let Line(_, content) = self.read_response(status::FILE)?;

        match SIZE_RE.captures(&content) {
            Some(caps) => Ok(Some(caps[1].parse().unwrap())),
            None => Ok(None),
        }
    }

    fn write_str<S: AsRef<str>>(&mut self, command: S) -> crate::Result<()> {
        if cfg!(feature = "debug_print") {
            print!("CMD {}", command.as_ref());
        }

        Ok(self
            .reader
            .get_mut()
            .write_all(command.as_ref().as_bytes())?)
    }

    pub fn read_response(&mut self, expected_code: u32) -> crate::Result<Line> {
        self.read_response_in(&[expected_code])
    }

    /// Retrieve single line response
    pub fn read_response_in(&mut self, expected_code: &[u32]) -> crate::Result<Line> {
        let mut line = String::with_capacity(5);
        self.reader.read_line(&mut line)?;

        if cfg!(feature = "debug_print") {
            print!("FTP {}", line);
        }

        if line.len() < 5 {
            return Err(FtpError::InvalidResponse(
                "error: could not read reply code".to_owned(),
            ));
        }

        let code: u32 = line[0..3].parse().map_err(|err| {
            FtpError::InvalidResponse(format!("error: could not parse reply code: {}", err))
        })?;

        // multiple line reply
        // loop while the line does not begin with the code and a space
        let expected = format!("{} ", &line[0..3]);
        while line.len() < 5 || line[0..4] != expected {
            line.clear();
            if let Err(e) = self.reader.read_line(&mut line) {
                return Err(FtpError::ConnectionError(e));
            }

            if cfg!(feature = "debug_print") {
                print!("FTP {}", line);
            }
        }

        line = String::from(line.trim());

        if expected_code.iter().any(|ec| code == *ec) {
            Ok(Line(code, line))
        } else {
            Err(FtpError::InvalidResponse(format!(
                "Expected code {:?}, got response: {}",
                expected_code, line
            )))
        }
    }
}
