#![macro_use]
#![allow(incomplete_features)]
#![feature(async_fn_in_trait)]
use embedded_io::BufRead as _;
use embedded_io_adapters::{std::FromStd, tokio_1::FromTokio};
use embedded_io_async::BufRead as _;
use embedded_io_async::Write;
use rand::rngs::OsRng;
use std::net::SocketAddr;
use std::sync::Once;

mod tlsserver;

static LOG_INIT: Once = Once::new();
static INIT: Once = Once::new();
static mut ADDR: Option<SocketAddr> = None;

fn init_log() {
    LOG_INIT.call_once(|| {
        env_logger::init();
    });
}

fn setup() -> SocketAddr {
    use mio::net::TcpListener;
    init_log();
    INIT.call_once(|| {
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

#[ignore]
#[tokio::test]
async fn test_google() {
    use embedded_tls::*;
    use tokio::net::TcpStream;

    init_log();

    let stream = TcpStream::connect("google.com:443")
        .await
        .expect("error connecting to server");

    log::info!("Connected");
    let mut read_record_buffer = [0; 16384];
    let mut write_record_buffer = [0; 16384];
    let config = TlsConfig::new().with_server_name("google.com");

    let mut tls: TlsConnection<FromTokio<TcpStream>, Aes128GcmSha256> = TlsConnection::new(
        FromTokio::new(stream),
        &mut read_record_buffer,
        &mut write_record_buffer,
    );

    let mut rng = OsRng;
    let open_fut = tls.open::<OsRng, NoVerify>(TlsContext::new(&config, &mut rng));
    log::info!("SIZE of open fut is {}", core::mem::size_of_val(&open_fut));
    open_fut.await.expect("error establishing TLS connection");
    log::info!("Established");

    tls.write_all(b"GET / HTTP/1.0\r\n\r\n")
        .await
        .expect("error writing data");
    tls.flush().await.expect("error flushing data");

    let mut rx_buf = [0; 4096];
    let sz = tls.read(&mut rx_buf).await.expect("error reading data");
    log::info!("Read {} bytes: {:?}", sz, &rx_buf[..sz]);

    tls.close()
        .await
        .map_err(|(_, e)| e)
        .expect("error closing session");
}

#[tokio::test]
async fn test_ping() {
    use embedded_tls::*;
    use tokio::net::TcpStream;
    let addr = setup();
    let pem = include_str!("data/ca-cert.pem");
    let der = pem_parser::pem_to_der(pem);

    let stream = TcpStream::connect(addr)
        .await
        .expect("error connecting to server");

    log::info!("Connected");
    let mut read_record_buffer = [0; 16384];
    let mut write_record_buffer = [0; 16384];
    let config = TlsConfig::new()
        .with_ca(Certificate::X509(&der[..]))
        .with_server_name("localhost");

    let mut tls: TlsConnection<FromTokio<TcpStream>, Aes128GcmSha256> = TlsConnection::new(
        FromTokio::new(stream),
        &mut read_record_buffer,
        &mut write_record_buffer,
    );

    log::info!("SIZE of connection is {}", core::mem::size_of_val(&tls));

    let mut rng = OsRng;
    let open_fut = tls.open::<OsRng, NoVerify>(TlsContext::new(&config, &mut rng));
    log::info!("SIZE of open fut is {}", core::mem::size_of_val(&open_fut));
    open_fut.await.expect("error establishing TLS connection");
    log::info!("Established");

    let write_fut = tls.write(b"ping");
    log::info!(
        "SIZE of write fut is {}",
        core::mem::size_of_val(&write_fut)
    );
    write_fut.await.expect("error writing data");
    tls.flush().await.expect("error flushing data");

    // Make sure reading into a 0 length buffer doesn't loop
    let mut rx_buf = [0; 0];
    let read_fut = tls.read(&mut rx_buf);
    log::info!("SIZE of read fut is {}", core::mem::size_of_val(&read_fut));
    let sz = read_fut.await.expect("error reading data");
    assert_eq!(sz, 0);

    let mut rx_buf = [0; 4096];
    let read_fut = tls.read(&mut rx_buf);
    log::info!("SIZE of read fut is {}", core::mem::size_of_val(&read_fut));
    let sz = read_fut.await.expect("error reading data");
    assert_eq!(4, sz);
    assert_eq!(b"ping", &rx_buf[..sz]);
    log::info!("Read {} bytes: {:?}", sz, &rx_buf[..sz]);

    // Test that embedded-tls doesn't block if the buffer is empty.
    let mut rx_buf = [0; 0];
    let sz = tls.read(&mut rx_buf).await.expect("error reading data");
    assert_eq!(sz, 0);

    tls.close()
        .await
        .map_err(|(_, e)| e)
        .expect("error closing session");
}

#[tokio::test]
async fn test_ping_nocopy() {
    use embedded_tls::*;
    use tokio::net::TcpStream;
    let addr = setup();
    let pem = include_str!("data/ca-cert.pem");
    let der = pem_parser::pem_to_der(pem);

    let stream = TcpStream::connect(addr)
        .await
        .expect("error connecting to server");

    log::info!("Connected");
    let mut read_record_buffer = [0; 16384];
    let mut write_record_buffer = [0; 16384];
    let config = TlsConfig::new()
        .with_ca(Certificate::X509(&der[..]))
        .with_server_name("localhost");

    let mut tls: TlsConnection<FromTokio<TcpStream>, Aes128GcmSha256> = TlsConnection::new(
        FromTokio::new(stream),
        &mut read_record_buffer,
        &mut write_record_buffer,
    );

    log::info!("SIZE of connection is {}", core::mem::size_of_val(&tls));

    let mut rng = OsRng;
    let open_fut = tls.open::<OsRng, NoVerify>(TlsContext::new(&config, &mut rng));
    log::info!("SIZE of open fut is {}", core::mem::size_of_val(&open_fut));
    open_fut.await.expect("error establishing TLS connection");
    log::info!("Established");

    let write_fut = tls.write(b"data to echo");
    log::info!(
        "SIZE of write fut is {}",
        core::mem::size_of_val(&write_fut)
    );
    write_fut.await.expect("error writing data");
    tls.flush().await.expect("error flushing data");

    {
        let mut buf = tls.read_buffered().await.expect("error reading data");
        log::info!("Read bytes: {:?}", buf.peek_all());

        let read_bytes = buf.pop(2);
        assert_eq!(b"da", read_bytes);

        let read_bytes = buf.pop(2);
        assert_eq!(b"ta", read_bytes);
    }

    {
        let mut buf = tls.read_buffered().await.expect("error reading data");
        assert_eq!(b" to ", buf.pop(4));
    }

    {
        let mut buf = tls.read_buffered().await.expect("error reading data");
        let read_bytes = buf.pop_all();
        assert_eq!(b"echo", read_bytes);
    }

    tls.close()
        .await
        .map_err(|(_, e)| e)
        .expect("error closing session");
}

#[tokio::test]
async fn test_ping_nocopy_bufread() {
    use embedded_tls::*;
    use tokio::net::TcpStream;

    let addr = setup();
    let pem = include_str!("data/ca-cert.pem");
    let der = pem_parser::pem_to_der(pem);

    let stream = TcpStream::connect(addr)
        .await
        .expect("error connecting to server");

    log::info!("Connected");
    let mut read_record_buffer = [0; 16384];
    let mut write_record_buffer = [0; 16384];
    let config = TlsConfig::new()
        .with_ca(Certificate::X509(&der[..]))
        .with_server_name("localhost");

    let mut tls: TlsConnection<FromTokio<TcpStream>, Aes128GcmSha256> = TlsConnection::new(
        FromTokio::new(stream),
        &mut read_record_buffer,
        &mut write_record_buffer,
    );

    tls.open::<OsRng, NoVerify>(TlsContext::new(&config, &mut OsRng))
        .await
        .expect("error establishing TLS connection");
    log::info!("Established");

    tls.write(b"ping").await.expect("error writing data");
    tls.flush().await.expect("error flushing data");

    let buf = tls.fill_buf().await.expect("error reading data");

    assert_eq!(b"ping", buf);
    log::info!("Read bytes: {:?}", buf);

    let len = buf.len();
    tls.consume(len);

    tls.close()
        .await
        .map_err(|(_, e)| e)
        .expect("error closing session");
}

#[test]
fn test_blocking_ping() {
    use embedded_tls::blocking::*;
    use std::net::TcpStream;

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

    let mut tls: TlsConnection<FromStd<TcpStream>, Aes128GcmSha256> = TlsConnection::new(
        FromStd::new(stream),
        &mut read_record_buffer,
        &mut write_record_buffer,
    );

    tls.open::<OsRng, NoVerify>(TlsContext::new(&config, &mut OsRng))
        .expect("error establishing TLS connection");
    log::info!("Established");

    tls.write(b"ping").expect("error writing data");
    tls.flush().expect("error flushing data");

    // Make sure reading into a 0 length buffer doesn't loop
    let mut rx_buf = [0; 0];
    let sz = tls.read(&mut rx_buf).expect("error reading data");
    assert_eq!(sz, 0);

    let mut rx_buf = [0; 4096];
    let sz = tls.read(&mut rx_buf).expect("error reading data");
    assert_eq!(4, sz);
    assert_eq!(b"ping", &rx_buf[..sz]);
    log::info!("Read {} bytes: {:?}", sz, &rx_buf[..sz]);

    // Test that embedded-tls doesn't block if the buffer is empty.
    let mut rx_buf = [0; 0];
    let sz = tls.read(&mut rx_buf).expect("error reading data");
    assert_eq!(sz, 0);

    tls.close()
        .map_err(|(_, e)| e)
        .expect("error closing session");
}

#[test]
fn test_blocking_ping_nocopy() {
    use embedded_tls::blocking::*;
    use std::net::TcpStream;

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

    let mut tls: TlsConnection<FromStd<TcpStream>, Aes128GcmSha256> = TlsConnection::new(
        FromStd::new(stream),
        &mut read_record_buffer,
        &mut write_record_buffer,
    );

    tls.open::<OsRng, NoVerify>(TlsContext::new(&config, &mut OsRng))
        .expect("error establishing TLS connection");
    log::info!("Established");

    tls.write(b"ping").expect("error writing data");
    tls.flush().expect("error flushing data");

    let mut buf = tls.read_buffered().expect("error reading data");
    log::info!("Read bytes: {:?}", buf.peek_all());

    let read_bytes = buf.pop(2);
    assert_eq!(b"pi", read_bytes);
    let read_bytes = buf.pop_all();
    assert_eq!(b"ng", read_bytes);

    core::mem::drop(buf);

    tls.close()
        .map_err(|(_, e)| e)
        .expect("error closing session");
}

#[test]
fn test_blocking_ping_nocopy_bufread() {
    use embedded_tls::blocking::*;
    use std::net::TcpStream;

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

    let mut tls: TlsConnection<FromStd<TcpStream>, Aes128GcmSha256> = TlsConnection::new(
        FromStd::new(stream),
        &mut read_record_buffer,
        &mut write_record_buffer,
    );

    tls.open::<OsRng, NoVerify>(TlsContext::new(&config, &mut OsRng))
        .expect("error establishing TLS connection");
    log::info!("Established");

    tls.write(b"ping").expect("error writing data");
    tls.flush().expect("error flushing data");

    let buf = tls.fill_buf().expect("error reading data");

    assert_eq!(b"ping", buf);
    log::info!("Read bytes: {:?}", buf);

    let len = buf.len();
    tls.consume(len);

    tls.close()
        .map_err(|(_, e)| e)
        .expect("error closing session");
}
