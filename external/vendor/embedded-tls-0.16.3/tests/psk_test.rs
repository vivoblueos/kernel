#![macro_use]
#![allow(incomplete_features)]
#![feature(async_fn_in_trait)]
use embedded_io_adapters::tokio_1::FromTokio;
use embedded_tls::*;
use openssl::ssl;
use rand::rngs::OsRng;
use std::io::{Read, Write};
use std::net::SocketAddr;
use std::net::TcpListener;
use std::sync::Once;
use tokio::net::TcpStream;
use tokio::task::JoinHandle;
use tokio::time::timeout;
use tokio::time::Duration;

static INIT: Once = Once::new();

fn setup() -> (SocketAddr, JoinHandle<()>) {
    INIT.call_once(|| {
        env_logger::init();
    });

    const DEFAULT_CIPHERS: &[&str] = &["PSK"];
    let mut builder =
        ssl::SslAcceptor::mozilla_intermediate_v5(ssl::SslMethod::tls_server()).unwrap();
    builder
        .set_private_key_file("tests/data/server-key.pem", ssl::SslFiletype::PEM)
        .unwrap();
    builder
        .set_certificate_chain_file("tests/data/server-cert.pem")
        .unwrap();
    builder
        .set_min_proto_version(Some(ssl::SslVersion::TLS1_3))
        .unwrap();
    builder.set_cipher_list(&DEFAULT_CIPHERS.join(",")).unwrap();
    builder.set_psk_server_callback(move |_ssl, identity, secret_mut| {
        if let Some(b"vader") = identity {
            secret_mut[..4].copy_from_slice(&[0xaa, 0xbb, 0xcc, 0xdd]);
            Ok(4)
        } else {
            Ok(0)
        }
    });
    let acceptor = builder.build();

    let addr: SocketAddr = "127.0.0.1:0".parse().unwrap();

    let listener = TcpListener::bind(addr).expect("cannot listen on port");
    let addr = listener
        .local_addr()
        .expect("error retrieving socket address");

    let h = tokio::task::spawn_blocking(move || {
        let (stream, _) = listener.accept().unwrap();
        let mut conn = acceptor.accept(stream).unwrap();
        let mut buf = [0; 64];
        let len = conn.read(&mut buf[..]).unwrap();
        conn.write(&buf[..len]).unwrap();
    });
    (addr, h)
}

#[tokio::test(flavor = "multi_thread")]
async fn test_psk_open() {
    let (addr, h) = setup();
    timeout(Duration::from_secs(120), async move {
        println!("Connecting...");
        let stream = TcpStream::connect(addr)
            .await
            .expect("error connecting to server");

        println!("Connected");
        let mut read_record_buffer = [0; 16384];
        let mut write_record_buffer = [0; 16384];
        let config = TlsConfig::new()
            .with_psk(&[0xaa, 0xbb, 0xcc, 0xdd], &[b"vader"])
            .with_server_name("localhost");

        let mut tls: TlsConnection<FromTokio<TcpStream>, Aes128GcmSha256> = TlsConnection::new(
            FromTokio::new(stream),
            &mut read_record_buffer,
            &mut write_record_buffer,
        );

        let mut rng = OsRng;
        assert!(tls
            .open::<OsRng, NoVerify>(TlsContext::new(&config, &mut rng))
            .await
            .is_ok());
        println!("TLS session opened");

        tls.write(b"ping").await.unwrap();
        tls.flush().await.unwrap();

        println!("TLS data written");
        let mut rx = [0; 4];
        let l = tls.read(&mut rx[..]).await.unwrap();

        println!("TLS data read");
        assert_eq!(4, l);
        assert_eq!(b"ping", &rx[..l]);

        h.await.unwrap();
    })
    .await
    .unwrap();
}
