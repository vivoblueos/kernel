use super::*;
use heapless::{String, Vec};

// NOTE: this struct is re-exported
/// Websocket details extracted from the http header
pub struct WebSocketContext {
    /// The list of sub protocols is restricted to a maximum of 3
    pub sec_websocket_protocol_list: Vec<WebSocketSubProtocol, 3>,
    /// The websocket key user to build the accept string to complete the opening handshake
    pub sec_websocket_key: WebSocketKey,
}

// NOTE: this function is re-exported
/// Reads an http header and extracts websocket specific information from it.
///
/// # Examples
/// ```
/// use embedded_websocket as ws;
/// let client_request = "GET /chat HTTP/1.1
/// Host: myserver.example.com
/// Upgrade: websocket
/// Connection: Upgrade
/// Sec-WebSocket-Key: Z7OY1UwHOx/nkSz38kfPwg==
/// Origin: http://example.com
/// Sec-WebSocket-Protocol: chat, advancedchat
/// Sec-WebSocket-Version: 13
///
/// ";
///
/// let mut headers = [httparse::EMPTY_HEADER; 16];
/// let mut request = httparse::Request::new(&mut headers);
/// request.parse(client_request.as_bytes()).unwrap();
/// let headers = request.headers.iter().map(|f| (f.name, f.value));
/// let ws_context = ws::read_http_header(headers).unwrap().unwrap();
/// assert_eq!("Z7OY1UwHOx/nkSz38kfPwg==", ws_context.sec_websocket_key);
/// assert_eq!("chat", ws_context.sec_websocket_protocol_list.get(0).unwrap().as_str());
/// assert_eq!("advancedchat", ws_context.sec_websocket_protocol_list.get(1).unwrap().as_str());
///
/// ```
pub fn read_http_header<'a>(
    headers: impl Iterator<Item = (&'a str, &'a [u8])>,
) -> Result<Option<WebSocketContext>> {
    let mut sec_websocket_protocol_list: Vec<String<24>, 3> = Vec::new();
    let mut is_websocket_request = false;
    let mut sec_websocket_key = String::new();

    for (name, value) in headers {
        if name.eq_ignore_ascii_case("upgrade") {
            is_websocket_request = str::from_utf8(value)?.eq_ignore_ascii_case("websocket");
        } else if name.eq_ignore_ascii_case("sec-websocket-protocol") {
            // extract a csv list of supported sub protocols
            for item in str::from_utf8(value)?.split(", ") {
                if sec_websocket_protocol_list.len() < sec_websocket_protocol_list.capacity() {
                    // it is safe to unwrap here because we have checked
                    // the size of the list beforehand
                    sec_websocket_protocol_list
                        .push(String::from(item))
                        .unwrap();
                }
            }
        } else if name.eq_ignore_ascii_case("sec-websocket-key") {
            sec_websocket_key = String::from(str::from_utf8(value)?);
        }
    }

    if is_websocket_request {
        Ok(Some(WebSocketContext {
            sec_websocket_protocol_list,
            sec_websocket_key,
        }))
    } else {
        Ok(None)
    }
}

pub fn read_server_connect_handshake_response(
    sec_websocket_key: &WebSocketKey,
    from: &[u8],
) -> Result<(usize, Option<WebSocketSubProtocol>)> {
    let mut headers = [httparse::EMPTY_HEADER; 64];
    let mut response = httparse::Response::new(&mut headers);

    match response.parse(from)? {
        httparse::Status::Complete(len) => {
            match response.code {
                Some(101) => {
                    // we are ok
                }
                code => {
                    return Err(Error::HttpResponseCodeInvalid(code));
                }
            };

            let mut sec_websocket_protocol: Option<WebSocketSubProtocol> = None;
            for item in response.headers.iter() {
                if item.name.eq_ignore_ascii_case("sec-websocket-accept") {
                    let mut output = [0; 28];
                    build_accept_string(sec_websocket_key, &mut output)?;

                    let expected_accept_string = str::from_utf8(&output)?;
                    let actual_accept_string = str::from_utf8(item.value)?;

                    if actual_accept_string != expected_accept_string {
                        return Err(Error::AcceptStringInvalid);
                    }
                } else if item.name.eq_ignore_ascii_case("sec-websocket-protocol") {
                    sec_websocket_protocol = Some(String::from(str::from_utf8(item.value)?));
                }
            }

            Ok((len, sec_websocket_protocol))
        }
        httparse::Status::Partial => Err(Error::HttpHeaderIncomplete),
    }
}

pub fn build_connect_handshake_request(
    websocket_options: &WebSocketOptions,
    rng: &mut impl RngCore,
    to: &mut [u8],
) -> Result<(usize, WebSocketKey)> {
    let mut http_request: String<1024> = String::new();
    let mut key_as_base64: [u8; 24] = [0; 24];

    let mut key: [u8; 16] = [0; 16];
    rng.fill_bytes(&mut key);
    base64::encode_config_slice(key, base64::STANDARD, &mut key_as_base64);
    let sec_websocket_key: String<24> = String::from(str::from_utf8(&key_as_base64)?);

    http_request.push_str("GET ")?;
    http_request.push_str(websocket_options.path)?;
    http_request.push_str(" HTTP/1.1\r\nHost: ")?;
    http_request.push_str(websocket_options.host)?;
    http_request
        .push_str("\r\nUpgrade: websocket\r\nConnection: Upgrade\r\nSec-WebSocket-Key: ")?;
    http_request.push_str(sec_websocket_key.as_str())?;
    http_request.push_str("\r\nOrigin: ")?;
    http_request.push_str(websocket_options.origin)?;

    // turn sub protocol list into a CSV list
    if let Some(sub_protocols) = websocket_options.sub_protocols {
        http_request.push_str("\r\nSec-WebSocket-Protocol: ")?;
        for (i, sub_protocol) in sub_protocols.iter().enumerate() {
            http_request.push_str(sub_protocol)?;
            if i < (sub_protocols.len() - 1) {
                http_request.push_str(", ")?;
            }
        }
    }
    http_request.push_str("\r\n")?;

    if let Some(additional_headers) = websocket_options.additional_headers {
        for additional_header in additional_headers.iter() {
            http_request.push_str(additional_header)?;
            http_request.push_str("\r\n")?;
        }
    }

    http_request.push_str("Sec-WebSocket-Version: 13\r\n\r\n")?;
    to[..http_request.len()].copy_from_slice(http_request.as_bytes());
    Ok((http_request.len(), sec_websocket_key))
}

pub fn build_connect_handshake_response(
    sec_websocket_key: &WebSocketKey,
    sec_websocket_protocol: Option<&WebSocketSubProtocol>,
    to: &mut [u8],
) -> Result<usize> {
    let mut http_response: String<1024> = String::new();
    http_response.push_str(
        "HTTP/1.1 101 Switching Protocols\r\n\
         Connection: Upgrade\r\nUpgrade: websocket\r\n",
    )?;

    // if the user has specified a sub protocol
    if let Some(sec_websocket_protocol) = sec_websocket_protocol {
        http_response.push_str("Sec-WebSocket-Protocol: ")?;
        http_response.push_str(sec_websocket_protocol)?;
        http_response.push_str("\r\n")?;
    }

    let mut output = [0; 28];
    http::build_accept_string(sec_websocket_key, &mut output)?;
    let accept_string = str::from_utf8(&output)?;
    http_response.push_str("Sec-WebSocket-Accept: ")?;
    http_response.push_str(accept_string)?;
    http_response.push_str("\r\n\r\n")?;

    // save the response to the buffer
    to[..http_response.len()].copy_from_slice(http_response.as_bytes());
    Ok(http_response.len())
}

pub fn build_accept_string(sec_websocket_key: &WebSocketKey, output: &mut [u8]) -> Result<()> {
    // concatenate the key with a known websocket GUID (as per the spec)
    let mut accept_string: String<64> = String::new();
    accept_string.push_str(sec_websocket_key)?;
    accept_string.push_str("258EAFA5-E914-47DA-95CA-C5AB0DC85B11")?;

    // calculate the base64 encoded sha1 hash of the accept string above
    let mut sha1 = Sha1::new();
    sha1.update(&accept_string);
    let input = sha1.finalize();
    base64::encode_config_slice(input, base64::STANDARD, output); // no need for slices since the output WILL be 28 bytes
    Ok(())
}
