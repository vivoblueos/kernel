// Copyright (c) 2026 vivo Mobile Communication Co., Ltd.
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

//! Device wrapper for smoltcp compatibility.
//!
//! Wraps a `&mut dyn LinkLayer` so it can be used where smoltcp expects
//! a `impl Device`. With `trait_upcasting`, `dyn LinkLayer` can be passed
//! directly — this module is kept for cases where explicit wrapping is
//! needed.

use smoltcp::phy::{Device, DeviceCapabilities};
use smoltcp::time::Instant;

use crate::net::link::LinkLayer;

/// Wraps a `&mut dyn LinkLayer` for use as a `dyn Device`.
///
/// This is only needed when trait upcasting from `dyn LinkLayer` to
/// `dyn Device` is not sufficient. In most cases, pass `&mut *link`
/// directly.
pub struct DeviceWrapper<'a> {
    inner: &'a mut dyn LinkLayer,
}

impl<'a> DeviceWrapper<'a> {
    pub fn new(inner: &'a mut dyn LinkLayer) -> Self {
        DeviceWrapper { inner }
    }
}

impl<'a> Device for DeviceWrapper<'a> {
    type RxToken<'b> = <dyn LinkLayer as Device>::RxToken<'b> where Self: 'b;
    type TxToken<'b> = <dyn LinkLayer as Device>::TxToken<'b> where Self: 'b;

    fn receive(&mut self, timestamp: Instant) -> Option<(Self::RxToken<'_>, Self::TxToken<'_>)> {
        self.inner.receive(timestamp)
    }

    fn transmit(&mut self, timestamp: Instant) -> Option<Self::TxToken<'_>> {
        self.inner.transmit(timestamp)
    }

    fn capabilities(&self) -> DeviceCapabilities {
        self.inner.capabilities()
    }
}