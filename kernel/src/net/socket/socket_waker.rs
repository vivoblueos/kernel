// Copyright (c) 2025 vivo Mobile Communication Co., Ltd.
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

use alloc::{rc::Rc, string::String};
use blueos_infra::no_let_underscore::IgnoreResult;
use core::{
    cell::{Cell, RefCell},
    task::{RawWaker, RawWakerVTable, Waker},
};
use spin::Mutex;

use crate::net::connection::{Operation, NETSTACK_QUEUE};

pub struct SocketWaker {
    name: String,
    socket_operation: Rc<RefCell<Option<Operation>>>,
    socket_is_shutdown: Rc<Cell<bool>>,
}

impl SocketWaker {
    pub fn new(
        name: String,
        socket_operation: Option<Operation>,
        socket_is_shutdown: Rc<Cell<bool>>,
    ) -> Rc<Self> {
        Rc::new(SocketWaker {
            name,
            socket_operation: Rc::new(RefCell::new(socket_operation)),
            socket_is_shutdown,
        })
    }

    fn wake(&self) {
        if self.socket_is_shutdown.get() {
            log::debug!("[SocketWaker] {} socket is shutdown! ", self.name);
            return;
        }

        if let Some(socket_operation) = self.socket_operation.borrow_mut().take() {
            NETSTACK_QUEUE
                .enqueue(socket_operation)
                .map_err(|socket_operation| {
                    log::warn!("[SockerWaker] enqueue fail");
                    // TODO retry or release socket futex to unblock user thread
                })
                .ignore_result();
            log::debug!(
                "[SocketWaker] enqueue {} socket_operation success!",
                self.name
            )
        } else {
            log::debug!("[SocketWaker] find no {} socket_operation!", self.name)
        }
    }
}

fn closure_waker_vtable() -> &'static RawWakerVTable {
    &RawWakerVTable::new(
        |data| {
            let rc = unsafe { Rc::from_raw(data as *const SocketWaker) };
            let cloned = rc.clone();
            core::mem::forget(rc);
            RawWaker::new(Rc::into_raw(cloned) as *const (), closure_waker_vtable())
        },
        |data| {
            let rc = unsafe { Rc::from_raw(data as *const SocketWaker) };
            rc.wake();
        },
        |data| {
            let rc = unsafe { Rc::from_raw(data as *const SocketWaker) };
            rc.wake();
            core::mem::forget(rc);
        },
        |data| {
            unsafe { Rc::from_raw(data as *const SocketWaker) };
        },
    )
}

pub fn create_closure_waker(
    name: String,
    socket_operation: Option<Operation>,
    socket_is_shutdown: Rc<Cell<bool>>,
) -> Waker {
    let rc = SocketWaker::new(name, socket_operation, socket_is_shutdown);
    let raw_waker = RawWaker::new(Rc::into_raw(rc) as *const (), closure_waker_vtable());
    unsafe { Waker::from_raw(raw_waker) }
}
