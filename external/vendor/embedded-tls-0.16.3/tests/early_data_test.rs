#![macro_use]
#![allow(incomplete_features)]
#![feature(async_fn_in_trait)]
use embedded_io::{Read, Write};
use embedded_io_adapters::std::FromStd;
use rand_core::OsRng;
use std::net::SocketAddr;
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
            use tlsserver::*;

            let versions = &[&rustls::version::TLS13];

            let test_dir = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests");

            let certs = load_certs(&test_dir.join("data").join("server-cert.pem"));
            let privkey = load_private_key(&test_dir.join("data").join("server-key.pem"));

            let mut config = rustls::ServerConfig::builder()
                .with_cipher_suites(rustls::ALL_CIPHER_SUITES)
                .with_kx_groups(&rustls::ALL_KX_GROUPS)
                .with_protocol_versions(versions)
                .unwrap()
                .with_no_client_auth()
                .with_single_cert(certs, privkey)
                .unwrap();

            config.max_early_data_size = 512;

            run_with_config(listener, config);
        });
        unsafe { ADDR.replace(addr) };
    });
    unsafe { ADDR.unwrap() }
}

#[test]
fn early_data_ignored() {
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

    tls.write_all(b"ping").expect("Failed to write data");
    tls.flush().expect("Failed to flush");

    let mut buffer = [0; 4];
    tls.read_exact(&mut buffer).expect("Failed to read data");

    tls.close()
        .map_err(|(_, e)| e)
        .expect("error closing session");
}
