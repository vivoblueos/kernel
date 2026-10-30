#![no_std]
#![doc(html_logo_url = "https://avatars.githubusercontent.com/u/46717278")]
// bindgen generated code
#![allow(unnecessary_transmutes)]

pub mod c_types;
mod fmt;
pub mod include;

#[cfg(feature = "sys-logs")]
#[no_mangle]
extern "C" fn __esp_radio_printf(tag: *const core::ffi::c_char, msg: *const core::ffi::c_char) {
    unsafe {
        info!("{} {}", core::ffi::CStr::from_ptr(tag).to_str().unwrap(), core::ffi::CStr::from_ptr(msg).to_str().unwrap());
    }
}

#[cfg(not(feature = "sys-logs"))]
#[no_mangle]
extern "C" fn __esp_radio_printf(_tag: *const core::ffi::c_char, _msg: *const core::ffi::c_char) {
    // nothing
}
