# embedded-websocket
A lightweight rust websocket library for embedded systems `no_std`

This library facilitates the encoding and decoding of websocket messages and can be used for both clients and servers. The library is intended to be used in constrained memory environments like embedded microcontrollers which cannot reference the rust standard library. The library will work with arbitrarily small buffers regardless of websocket frame size as long as the websocket header can be read (2 - 14 bytes depending)

## no_std support

You can use this library without linking the rust standard library. In your Cargo.toml file make sure you set the default features to false.  For example:
```
embedded-websocket = { version = "x.x.x", default-features = false }
```
The optional (but recommended) [framer](./src/lib.rs) module allows you to ergonomically work with full websocket frames without having to deal with the complexities of fragmented data. If you use it you will have to implement the Read and Write traits in that module because they are not available in `no_std`. 

NOTE: If you get an error message like the following it means that you have not used `default-features = false` when declaring the dependency in your Cargo.toml file:
```
error[E0463]: can't find crate for `std`
  |
  = note: the `thumbv7m-none-eabi` target may not be installed
```

## Running the examples

The example below runs a websocket server that accepts client connections in a loop and returns back whatever text client sends. The client connects to the server, sends one "Hello, World!" message, waits for a response from the server then disconnects and terminates. Proper open and close handshakes are demonstrated.

To run the demo web server:

```
cargo run --example server
```
To run the demo websocket client:
```
cargo run --example client
```
or use this url in your browser `http://127.0.0.1:1337/`

## Working example project

See https://github.com/ninjasource/led-display-websocket-demo for a complete end-to-end example of this library working with and stm32 m3 bluepill MCU and an embedded ethernet card.


## Example websocket client usage:
The following example also found [here](./examples/client.rs) initiates a opening handshake, checks the handshake response, sends a short message, initiates a close handshake, checks the close handshake response and quits.

```rust
// open a TCP stream to localhost port 1337
let address = "127.0.0.1:1337";
println!("Connecting to: {}", address);
let mut stream = TcpStream::connect(address).map_err(FramerError::Io)?;
println!("Connected.");

let mut read_buf = [0; 4000];
let mut read_cursor = 0;
let mut write_buf = [0; 4000];
let mut frame_buf = [0; 4000];
let mut websocket = WebSocketClient::new_client(rand::thread_rng());

// initiate a websocket opening handshake
let websocket_options = WebSocketOptions {
    path: "/chat",
    host: "localhost",
    origin: "http://localhost:1337",
    sub_protocols: None,
    additional_headers: None,
};

let mut framer = Framer::new(
    &mut read_buf,
    &mut read_cursor,
    &mut write_buf,
    &mut websocket,
);
framer.connect(&mut stream, &websocket_options)?;

let message = "Hello, World!";
framer.write(
    &mut stream,
    WebSocketSendMessageType::Text,
    true,
    message.as_bytes(),
)?;

while let Some(s) = framer.read_text(&mut stream, &mut frame_buf)? {
    println!("Received: {}", s);

    // close the websocket after receiving the first reply
    framer.close(&mut stream, WebSocketCloseStatusCode::NormalClosure, None)?;
    println!("Sent close handshake");
}

println!("Connection closed");
```
## Example websocket server usage
The server example is a little too verbose to include in this readme, See [server example](./examples/server.rs)

## Async support

Async support is experimental and subject to significant API change.

## License 

Licensed under either MIT or Apache-2.0 at your option
