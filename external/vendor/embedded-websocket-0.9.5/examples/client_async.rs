use std::error::Error;

use tokio::net::TcpStream;
use tokio_util::codec::Framed;

use crate::common::MyCodec;
use embedded_websocket::{
    framer_async::{Framer, FramerError, ReadResult},
    WebSocketClient, WebSocketCloseStatusCode, WebSocketOptions, WebSocketSendMessageType,
};

mod common;

#[tokio::main]
async fn main() -> Result<(), FramerError<impl Error>> {
    // Connect to a peer
    let address = "127.0.0.1:1337";
    let mut buffer = [0u8; 4000];
    let stream = TcpStream::connect(address).await.map_err(FramerError::Io)?;
    let codec = MyCodec::new();
    let mut stream = Framed::new(stream, codec);
    let websocket = WebSocketClient::new_client(rand::thread_rng());

    // initiate a websocket opening handshake
    let websocket_options = WebSocketOptions {
        path: "/chat",
        host: "localhost",
        origin: "http://localhost:1337",
        sub_protocols: None,
        additional_headers: None,
    };

    let mut framer = Framer::new(websocket);

    framer
        .connect(&mut stream, &mut buffer, &websocket_options)
        .await?;

    println!("ws handshake complete");

    framer
        .write(
            &mut stream,
            &mut buffer,
            WebSocketSendMessageType::Text,
            true,
            "Hello, world".as_bytes(),
        )
        .await?;

    println!("sent message");

    while let Some(read_result) = framer.read(&mut stream, &mut buffer).await {
        let read_result = read_result?;
        match read_result {
            ReadResult::Text(text) => {
                println!("received text: {text}");

                framer
                    .close(
                        &mut stream,
                        &mut buffer,
                        WebSocketCloseStatusCode::NormalClosure,
                        None,
                    )
                    .await?
            }
            _ => { // ignore other kinds of messages
            }
        }
    }

    println!("closed");
    Ok(())
}
