#![macro_use]
#![allow(incomplete_features)]
#![feature(async_fn_in_trait)]
use embedded_io::{Read, Write};
use embedded_io_adapters::std::FromStd;
use rand_core::OsRng;
use std::net::{SocketAddr, TcpStream};
use std::sync::Once;

mod tlsserver;

static INIT: Once = Once::new();
static mut ADDR: Option<SocketAddr> = None;

fn setup() -> SocketAddr {
    use mio::net::TcpListener;
    INIT.call_once(|| {
        env_logger::init();

        let addr: SocketAddr = "127.0.0.1:12345".parse().unwrap();

        let listener = TcpListener::bind(addr).expect("cannot listen on port");
        let addr = listener
            .local_addr()
            .expect("error retrieving socket address");

        std::thread::spawn(move || {
            tlsserver::run(listener);
        });
        unsafe { ADDR.replace(addr) };
    });
    unsafe { ADDR.unwrap() }
}

pub struct Clonable<T: ?Sized>(std::sync::Arc<T>);

impl<T: ?Sized> Clone for Clonable<T> {
    fn clone(&self) -> Self {
        Self(self.0.clone())
    }
}

impl embedded_io::ErrorType for Clonable<TcpStream> {
    type Error = std::io::Error;
}

impl embedded_io::Read for Clonable<TcpStream> {
    fn read(&mut self, buf: &mut [u8]) -> Result<usize, Self::Error> {
        let mut stream = FromStd::new(self.0.as_ref());
        stream.read(buf)
    }
}

impl embedded_io::Write for Clonable<TcpStream> {
    fn write(&mut self, buf: &[u8]) -> Result<usize, Self::Error> {
        let mut stream = FromStd::new(self.0.as_ref());
        stream.write(buf)
    }
    fn flush(&mut self) -> Result<(), Self::Error> {
        let mut stream = FromStd::new(self.0.as_ref());
        stream.flush()
    }
}

#[test]
fn test_blocking_borrowed() {
    use embedded_tls::blocking::*;
    use std::net::TcpStream;
    use std::sync::Arc;
    let addr = setup();
    let pem = include_str!("data/ca-cert.pem");
    let der = pem_parser::pem_to_der(pem);

    let stream = TcpStream::connect(addr).expect("error connecting to server");

    log::info!("Connected");
    let mut read_record_buffer = [0; 16384];
    let mut write_record_buffer = [0; 16384];
    let config = TlsConfig::new()
        .with_ca(Certificate::X509(&der[..]))
        .with_server_name("localhost");

    let mut tls: TlsConnection<Clonable<TcpStream>, Aes128GcmSha256> = TlsConnection::new(
        Clonable(Arc::new(stream)),
        &mut read_record_buffer,
        &mut write_record_buffer,
    );

    tls.open::<OsRng, NoVerify>(TlsContext::new(&config, &mut OsRng))
        .expect("error establishing TLS connection");

    let mut state = SplitConnectionState::default();
    let (mut reader, mut writer) = tls.split_with(&mut state);

    std::thread::scope(|scope| {
        scope.spawn(|| {
            let mut buffer = [0; 4];
            reader.read_exact(&mut buffer).expect("Failed to read data");
        });
        scope.spawn(|| {
            writer.write(b"ping").expect("Failed to write data");
            writer.flush().expect("Failed to flush");
        });
    });

    let tls = TlsConnection::unsplit(reader, writer);

    tls.close()
        .map_err(|(_, e)| e)
        .expect("error closing session");
}

#[test]
fn test_blocking_managed() {
    use embedded_tls::blocking::*;
    use std::net::TcpStream;
    use std::sync::Arc;
    let addr = setup();
    let pem = include_str!("data/ca-cert.pem");
    let der = pem_parser::pem_to_der(pem);

    let stream = TcpStream::connect(addr).expect("error connecting to server");

    log::info!("Connected");
    let mut read_record_buffer = [0; 16384];
    let mut write_record_buffer = [0; 16384];
    let config = TlsConfig::new()
        .with_ca(Certificate::X509(&der[..]))
        .with_server_name("localhost");

    let mut tls: TlsConnection<Clonable<TcpStream>, Aes128GcmSha256> = TlsConnection::new(
        Clonable(Arc::new(stream)),
        &mut read_record_buffer,
        &mut write_record_buffer,
    );

    tls.open::<OsRng, NoVerify>(TlsContext::new(&config, &mut OsRng))
        .expect("error establishing TLS connection");

    let (mut reader, mut writer) = tls.split();

    std::thread::scope(|scope| {
        scope.spawn(|| {
            let mut buffer = [0; 4];
            reader.read_exact(&mut buffer).expect("Failed to read data");
        });
        scope.spawn(|| {
            writer.write(b"ping").expect("Failed to write data");
            writer.flush().expect("Failed to flush");
        });
    });

    let tls = TlsConnection::unsplit(reader, writer);

    tls.close()
        .map_err(|(_, e)| e)
        .expect("error closing session");
}
