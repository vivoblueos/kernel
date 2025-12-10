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
use super::{ISpinLock, SpinLock, SpinLockGuard};
use crate::{
    allocator,
    error::{code, Error},
    irq,
    scheduler::{self, wait_queue, InsertMode, WaitEntry, WaitQueue},
    support::align_up_size,
    thread,
    time::{self, NO_WAITING, WAITING_FOREVER},
    types::{impl_simple_intrusive_adapter, Arc},
};
use alloc::alloc::{alloc, dealloc, Layout};
use blueos_infra::ringbuffer::BoxedRingBuffer;
use core::{
    ops::DerefMut,
    slice,
    sync::atomic::{AtomicU32, Ordering},
};

impl_simple_intrusive_adapter!(OffsetOfLock, MessageQueue, lock);

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub enum SendMode {
    Normal = 0,
    Urgent = 1,
}

pub const SEND_TYPE: usize = 0;
pub const RECV_TYPE: usize = 1;

#[derive(Debug)]
pub struct MessageQueue {
    node_size: usize,
    node_count: u32,
    accessible_count: [AtomicU32; 2],
    // pend_queues contain a receiver pending queue and a sender pending queue
    pend_queues: [SpinLock<WaitQueue>; 2],
    queue_buffer: BoxedRingBuffer,
    // use spinlock to protect the structure,
    lock: ISpinLock<MessageQueue, OffsetOfLock>,
}

impl MessageQueue {
    pub fn new(node_size: usize, node_count: u32, buf: *mut u8) -> Self {
        debug_assert!(node_size > 0 && node_count > 0);

        let node_align_size = align_up_size(node_size, core::mem::size_of::<usize>());
        let total_size = (node_align_size + core::mem::size_of::<usize>()) * node_count as usize;

        Self {
            node_size: node_align_size + core::mem::size_of::<usize>(),
            node_count,
            accessible_count: [AtomicU32::new(node_count), AtomicU32::new(0)],
            pend_queues: [const { SpinLock::new(WaitQueue::new()) }; 2],
            queue_buffer: if buf.is_null() {
                BoxedRingBuffer::new(total_size)
            } else {
                BoxedRingBuffer::new_with_mem(total_size, buf)
            },
            lock: ISpinLock::new(),
        }
    }

    pub fn init(&self) -> bool {
        self.pend_queues[SEND_TYPE].irqsave_lock().init()
            && self.pend_queues[RECV_TYPE].irqsave_lock().init()
    }

    #[inline]
    pub fn lock(&self) -> SpinLockGuard<'_, Self> {
        self.lock.irqsave_lock()
    }

    #[inline]
    pub fn node_info(&self) -> (usize, u32) {
        (self.node_size, self.node_count)
    }

    #[inline]
    pub fn sendable_count(&self) -> u32 {
        self.accessible_count[SEND_TYPE].load(Ordering::Relaxed)
    }

    #[inline]
    pub fn increment_sendable_count(&self) {
        self.accessible_count[SEND_TYPE].fetch_add(1, Ordering::Relaxed);
    }

    #[inline]
    pub fn decrement_sendable_count(&self) {
        self.accessible_count[SEND_TYPE].fetch_sub(1, Ordering::Relaxed);
    }

    #[inline]
    pub fn recvable_count(&self) -> u32 {
        self.accessible_count[RECV_TYPE].load(Ordering::Relaxed)
    }

    #[inline]
    pub fn increment_recvable_count(&self) {
        self.accessible_count[RECV_TYPE].fetch_add(1, Ordering::Relaxed);
    }

    #[inline]
    pub fn decrement_recvable_count(&self) {
        self.accessible_count[RECV_TYPE].fetch_sub(1, Ordering::Relaxed);
    }

    fn wakeup_pend_receiver(w: &mut SpinLockGuard<'_, WaitQueue>) -> bool {
        for next in w.iter() {
            let t = next.thread.clone();
            if let Some(timer) = &t.timer {
                timer.stop();
            }
            let ok = scheduler::queue_ready_thread(thread::SUSPENDED, t);
            if ok {
                return true;
            }
        }
        return false;
    }

    pub fn send(
        &self,
        buffer: &[u8],
        size: usize,
        timeout: usize,
        urgent: SendMode,
    ) -> Result<(), Error> {
        if buffer.len() < size {
            return Err(code::EINVAL);
        }
        let head_size = core::mem::size_of::<usize>();
        let mut timeout = timeout;

        if size > (self.node_size - head_size) {
            return Err(code::EOVERFLOW);
        }

        let this_thread = scheduler::current_thread();
        let mut queue = self.lock();
        let mut send_queue = self.pend_queues[SEND_TYPE].irqsave_lock();
        while self.sendable_count() == 0 {
            if timeout == NO_WAITING {
                return Err(code::ETIMEDOUT);
            }
            if irq::is_in_irq() {
                return Err(code::ENOTSUP);
            }
            let mut ticks = time::TickTime::now().as_ticks();
            send_queue.take_irq_guard(&mut queue);
            drop(queue);
            let mut borrowed_wait_entry;
            let reached_deadline;
            {
                let mut wait_entry = WaitEntry::new(this_thread.clone());
                borrowed_wait_entry = wait_queue::insert(
                    send_queue.deref_mut(),
                    &mut wait_entry,
                    InsertMode::InsertToEnd,
                )
                .unwrap();
                reached_deadline = scheduler::suspend_me_with_timeout(send_queue, timeout);
                queue = self.lock();
                send_queue = self.pend_queues[SEND_TYPE].irqsave_lock();
                borrowed_wait_entry = send_queue.pop(borrowed_wait_entry).unwrap();
            }
            drop(borrowed_wait_entry);
            if reached_deadline {
                return Err(code::ETIMEDOUT);
            }
            if timeout != WAITING_FOREVER {
                ticks = time::TickTime::now().as_ticks().saturating_sub(ticks);
                timeout = timeout.saturating_sub(ticks);
            }
        }
        drop(send_queue);
        queue.decrement_sendable_count();
        let mut sender = unsafe { queue.queue_buffer.writer() };
        let dst: &mut [u8];
        if urgent == SendMode::Normal {
            dst = sender.push_slice();
            dst[head_size..(head_size + size)].copy_from_slice(&buffer[0..size]);
            unsafe { *(dst.as_ptr() as *mut usize) = size };
            sender.push_done(queue.node_size);
        } else {
            let [(end, len0), (start, len1)] = sender.push_bufs();
            if len1 != 0 {
                debug_assert!(len1 >= queue.node_size);
                dst = unsafe {
                    slice::from_raw_parts_mut(start.add(len1 - queue.node_size), queue.node_size)
                };
            } else {
                debug_assert!(len0 >= queue.node_size);
                dst = unsafe {
                    slice::from_raw_parts_mut(end.add(len0 - queue.node_size), queue.node_size)
                };
            }

            dst[head_size..(head_size + size)].copy_from_slice(&buffer[0..size]);
            unsafe { *(dst.as_ptr() as *mut usize) = size };
            sender.push_front_done(queue.node_size);
        }

        queue.increment_recvable_count();
        let mut recv_queue = queue.pend_queues[RECV_TYPE].irqsave_lock();
        if MessageQueue::wakeup_pend_receiver(&mut recv_queue) {
            drop(recv_queue);
            drop(queue);
            scheduler::yield_me_now_or_later();
        }

        Ok(())
    }

    pub fn recv(&self, buffer: &mut [u8], size: usize, timeout: usize) -> Result<(), Error> {
        if buffer.len() < size || size == 0 {
            return Err(code::EINVAL);
        }
        let mut cpysize = size;
        let head_size = core::mem::size_of::<usize>();
        let mut timeout = timeout;

        let this_thread = scheduler::current_thread();
        let mut queue = self.lock();
        let mut recv_queue = self.pend_queues[RECV_TYPE].irqsave_lock();
        while self.recvable_count() == 0 {
            if timeout == NO_WAITING {
                return Err(code::ETIMEDOUT);
            }
            if irq::is_in_irq() {
                return Err(code::ENOTSUP);
            }
            let mut ticks = time::TickTime::now().as_ticks();
            recv_queue.take_irq_guard(&mut queue);
            drop(queue);
            let mut borrowed_wait_entry;
            let reached_deadline;
            {
                let mut wait_entry = WaitEntry::new(this_thread.clone());
                borrowed_wait_entry = wait_queue::insert(
                    recv_queue.deref_mut(),
                    &mut wait_entry,
                    InsertMode::InsertToEnd,
                )
                .unwrap();
                reached_deadline = scheduler::suspend_me_with_timeout(recv_queue, timeout);
                queue = self.lock();
                recv_queue = self.pend_queues[RECV_TYPE].irqsave_lock();
                borrowed_wait_entry = recv_queue.pop(borrowed_wait_entry).unwrap();
            }
            drop(borrowed_wait_entry);
            if reached_deadline {
                return Err(code::ETIMEDOUT);
            }
            if timeout != WAITING_FOREVER {
                ticks = time::TickTime::now().as_ticks().saturating_sub(ticks);
                timeout = timeout.saturating_sub(ticks);
            }
        }
        drop(recv_queue);
        queue.decrement_recvable_count();
        let mut receiver = unsafe { queue.queue_buffer.reader() };
        let src = receiver.pop_slice();
        let msg_size = unsafe { *(src.as_ptr() as *const usize) };
        if msg_size < cpysize {
            cpysize = msg_size;
        }

        buffer[0..cpysize].copy_from_slice(&src[head_size..(head_size + cpysize)]);
        receiver.pop_done(queue.node_size);
        queue.increment_sendable_count();

        let mut send_queue = queue.pend_queues[SEND_TYPE].irqsave_lock();
        if MessageQueue::wakeup_pend_receiver(&mut send_queue) {
            drop(send_queue);
            drop(queue);
            scheduler::yield_me_now_or_later();
        }
        Ok(())
    }

    pub fn reset(&self) {
        let mut queue = self.lock();

        // Wakeup sender thread.
        let mut send_queue = self.pend_queues[SEND_TYPE].irqsave_lock();
        for entry in send_queue.iter() {
            scheduler::queue_ready_thread(thread::SUSPENDED, entry.thread.clone());
        }
        drop(send_queue);
        // Reset ringbuffer.
        queue.queue_buffer.reset();

        self.accessible_count[SEND_TYPE].store(self.node_count, Ordering::Relaxed);
        self.accessible_count[RECV_TYPE].store(0, Ordering::Relaxed);

        drop(queue);
        scheduler::yield_me_now_or_later();
    }
}

impl !Send for MessageQueue {}
unsafe impl Sync for MessageQueue {}

#[cfg(test)]
mod tests {
    use super::*;
    use blueos_test_macro::test;
    use core::ptr;

    #[test]
    fn test_message_init() {
        let queue = MessageQueue::new(4, 4, ptr::null_mut());

        // Test initialization
        let result = queue.init();
        assert!(result);

        // Test multiple initializations
        let result2 = queue.init();
        assert!(!result2);
    }

    #[test]
    fn test_message_send() {
        let queue = MessageQueue::new(4, 4, ptr::null_mut());

        // Test initialization
        let result = queue.init();
        assert!(result);

        let mut buffer = [0u8; 4];
        let result = queue.send(&buffer, 4, NO_WAITING, SendMode::Normal);
        assert!(result.is_ok());
        assert_eq!(queue.sendable_count(), 3);
        assert_eq!(queue.recvable_count(), 1);

        let result = queue.send(&buffer, 4, NO_WAITING, SendMode::Normal);
        assert!(result.is_ok());
        assert_eq!(queue.sendable_count(), 2);
        assert_eq!(queue.recvable_count(), 2);

        let result = queue.send(&buffer, 4, NO_WAITING, SendMode::Normal);
        assert!(result.is_ok());
        assert_eq!(queue.sendable_count(), 1);
        assert_eq!(queue.recvable_count(), 3);

        let result = queue.send(&buffer, 4, NO_WAITING, SendMode::Normal);
        assert!(result.is_ok());
        assert_eq!(queue.sendable_count(), 0);
        assert_eq!(queue.recvable_count(), 4);

        let result = queue.send(&buffer, 4, NO_WAITING, SendMode::Normal);
        assert!(result.is_err());
        assert_eq!(queue.sendable_count(), 0);
        assert_eq!(queue.recvable_count(), 4);
    }

    #[test]
    fn test_message_send_urgent() {
        let queue = MessageQueue::new(4, 4, ptr::null_mut());

        // Test initialization
        let result = queue.init();
        assert!(result);

        let mut buffer = [0u8; 4];
        let result = queue.send(&buffer, 4, NO_WAITING, SendMode::Normal);
        assert!(result.is_ok());
        assert_eq!(queue.sendable_count(), 3);
        assert_eq!(queue.recvable_count(), 1);

        let result = queue.send(&buffer, 4, NO_WAITING, SendMode::Urgent);
        assert!(result.is_ok());
        assert_eq!(queue.sendable_count(), 2);
        assert_eq!(queue.recvable_count(), 2);

        let result = queue.send(&buffer, 4, NO_WAITING, SendMode::Normal);
        assert!(result.is_ok());
        assert_eq!(queue.sendable_count(), 1);
        assert_eq!(queue.recvable_count(), 3);

        let result = queue.send(&buffer, 4, NO_WAITING, SendMode::Urgent);
        assert!(result.is_ok());
        assert_eq!(queue.sendable_count(), 0);
        assert_eq!(queue.recvable_count(), 4);

        let result = queue.send(&buffer, 4, NO_WAITING, SendMode::Urgent);
        assert!(result.is_err());
        assert_eq!(queue.sendable_count(), 0);
        assert_eq!(queue.recvable_count(), 4);
    }

    #[test]
    fn test_message_send_recv() {
        let queue = MessageQueue::new(4, 4, ptr::null_mut());

        // Test initialization
        let result = queue.init();
        assert!(result);

        let buffer = [1u8; 4];
        let result = queue.send(&buffer, 4, NO_WAITING, SendMode::Normal);
        assert!(result.is_ok());
        assert_eq!(queue.sendable_count(), 3);
        assert_eq!(queue.recvable_count(), 1);

        let buffer = [3u8; 4];
        let result = queue.send(&buffer, 4, NO_WAITING, SendMode::Urgent);
        assert!(result.is_ok());
        assert_eq!(queue.sendable_count(), 2);
        assert_eq!(queue.recvable_count(), 2);

        let mut buffer = [0u8; 4];
        let result = queue.recv(&mut buffer, 4, NO_WAITING);
        assert!(result.is_ok());
        assert_eq!(buffer, [3u8, 3u8, 3u8, 3u8]);
        assert_eq!(queue.sendable_count(), 3);
        assert_eq!(queue.recvable_count(), 1);

        let result = queue.recv(&mut buffer, 4, NO_WAITING);
        assert!(result.is_ok());
        assert_eq!(buffer, [1u8, 1u8, 1u8, 1u8]);
        assert_eq!(queue.sendable_count(), 4);
        assert_eq!(queue.recvable_count(), 0);
    }

    #[test]
    fn test_message_send_outtime() {
        let queue = MessageQueue::new(4, 2, ptr::null_mut());

        // Test initialization
        let result = queue.init();
        assert!(result);

        let buffer = [1u8; 4];
        let result = queue.send(&buffer, 4, 10, SendMode::Normal);
        assert!(result.is_ok());
        assert_eq!(queue.sendable_count(), 1);
        assert_eq!(queue.recvable_count(), 1);

        let buffer = [3u8; 4];
        let result = queue.send(&buffer, 4, 10, SendMode::Urgent);
        assert!(result.is_ok());
        assert_eq!(queue.sendable_count(), 0);
        assert_eq!(queue.recvable_count(), 2);

        let buffer = [5u8; 4];
        let result = queue.send(&buffer, 4, 10, SendMode::Urgent);
        assert_eq!(result, Err(code::ETIMEDOUT));
    }

    #[test]
    fn test_message_recv_outtime() {
        let queue = MessageQueue::new(4, 2, ptr::null_mut());

        // Test initialization
        let result = queue.init();
        assert!(result);

        let buffer = [1u8; 4];
        let result = queue.send(&buffer, 4, 10, SendMode::Normal);
        assert!(result.is_ok());
        assert_eq!(queue.sendable_count(), 1);
        assert_eq!(queue.recvable_count(), 1);

        let buffer = [3u8; 4];
        let result = queue.send(&buffer, 4, 10, SendMode::Urgent);
        assert!(result.is_ok());
        assert_eq!(queue.sendable_count(), 0);
        assert_eq!(queue.recvable_count(), 2);

        let mut buffer = [0u8; 4];
        let result = queue.recv(&mut buffer, 4, 10);
        assert!(result.is_ok());
        assert_eq!(buffer, [3u8, 3u8, 3u8, 3u8]);
        assert_eq!(queue.sendable_count(), 1);
        assert_eq!(queue.recvable_count(), 1);

        let result = queue.recv(&mut buffer, 4, 10);
        assert!(result.is_ok());
        assert_eq!(buffer, [1u8, 1u8, 1u8, 1u8]);
        assert_eq!(queue.sendable_count(), 2);
        assert_eq!(queue.recvable_count(), 0);

        let result = queue.recv(&mut buffer, 4, 10);
        assert_eq!(result, Err(code::ETIMEDOUT));
    }

    #[test]
    fn test_message_multi_thread() {
        let queue = Arc::new(MessageQueue::new(4, 2, ptr::null_mut()));

        // Test initialization
        let result = queue.init();
        assert!(result);

        let recv_queue = queue.clone();
        let _ = thread::spawn(move || {
            let mut buffer = [0u8; 4];
            let result = recv_queue.recv(&mut buffer, 4, 10);
            assert!(result.is_ok());
            assert_eq!(buffer, [1u8, 1u8, 1u8, 1u8]);
            assert_eq!(recv_queue.sendable_count(), 2);
            assert_eq!(recv_queue.recvable_count(), 0);
        });
        let buffer = [1u8; 4];
        let result = queue.send(&buffer, 4, 10, SendMode::Normal);
        assert!(result.is_ok());
        scheduler::suspend_me_for(1);
    }

    #[test]
    fn test_message_multi_thread1() {
        let queue = Arc::new(MessageQueue::new(4, 2, ptr::null_mut()));

        // Test initialization
        let result = queue.init();
        assert!(result);

        let send_queue = queue.clone();
        let _ = thread::spawn(move || {
            let buffer = [1u8; 4];
            let result = send_queue.send(&buffer, 4, 0, SendMode::Normal);
            assert!(result.is_ok());
        });

        let mut buffer = [0u8; 4];
        let result = queue.recv(&mut buffer, 4, 10);
        assert!(result.is_ok());
        assert_eq!(buffer, [1u8, 1u8, 1u8, 1u8]);
        assert_eq!(queue.sendable_count(), 2);
        assert_eq!(queue.recvable_count(), 0);
        scheduler::yield_me();
    }

    #[test]
    fn test_message_multi_thread2() {
        let queue = Arc::new(MessageQueue::new(4, 1, ptr::null_mut()));

        // Test initialization
        let result = queue.init();
        assert!(result);

        let recv_queue = queue.clone();
        let _ = thread::spawn(move || {
            let mut buffer = [0u8; 4];
            let result = recv_queue.recv(&mut buffer, 4, 5);
            assert!(result.is_ok());
            assert_eq!(buffer, [1u8, 1u8, 1u8, 1u8]);
        });

        let buffer = [1u8; 4];
        let result = queue.send(&buffer, 4, 5, SendMode::Normal);
        assert!(result.is_ok());

        let buffer = [3u8; 4];
        let result = queue.send(&buffer, 4, 5, SendMode::Normal);
        assert!(result.is_ok());
        assert_eq!(queue.sendable_count(), 0);
        assert_eq!(queue.recvable_count(), 1);
        scheduler::yield_me();
    }

    #[test]
    fn test_message_send_recv_with_mem() {
        let layout = Layout::from_size_align(4 * 2 * core::mem::size_of::<usize>(), 8).unwrap();
        let mem = unsafe { alloc(layout) as *mut u8 };
        let queue = MessageQueue::new(4, 4, mem);

        // Test initialization
        let result = queue.init();
        assert!(result);

        let buffer = [1u8; 4];
        let result = queue.send(&buffer, 4, NO_WAITING, SendMode::Normal);
        assert!(result.is_ok());
        assert_eq!(queue.sendable_count(), 3);
        assert_eq!(queue.recvable_count(), 1);

        let buffer = [3u8; 4];
        let result = queue.send(&buffer, 4, NO_WAITING, SendMode::Urgent);
        assert!(result.is_ok());
        assert_eq!(queue.sendable_count(), 2);
        assert_eq!(queue.recvable_count(), 2);

        let mut buffer = [0u8; 4];
        let result = queue.recv(&mut buffer, 4, NO_WAITING);
        assert!(result.is_ok());
        assert_eq!(buffer, [3u8, 3u8, 3u8, 3u8]);
        assert_eq!(queue.sendable_count(), 3);
        assert_eq!(queue.recvable_count(), 1);

        let result = queue.recv(&mut buffer, 4, NO_WAITING);
        assert!(result.is_ok());
        assert_eq!(buffer, [1u8, 1u8, 1u8, 1u8]);
        assert_eq!(queue.sendable_count(), 4);
        assert_eq!(queue.recvable_count(), 0);
    }

    #[test]
    fn test_message_reset() {
        let layout = Layout::from_size_align(2 * 2 * core::mem::size_of::<usize>(), 8).unwrap();
        let mem = unsafe { alloc(layout) as *mut u8 };
        let queue = MessageQueue::new(4, 2, mem);

        // Test initialization
        let result = queue.init();
        assert!(result);

        let buffer = [1u8; 4];
        let result = queue.send(&buffer, 4, NO_WAITING, SendMode::Normal);
        assert!(result.is_ok());
        assert_eq!(queue.sendable_count(), 1);
        assert_eq!(queue.recvable_count(), 1);

        queue.reset();
        assert_eq!(queue.sendable_count(), 2);
        assert_eq!(queue.recvable_count(), 0);

        let buffer = [3u8; 4];
        let result = queue.send(&buffer, 4, NO_WAITING, SendMode::Urgent);
        assert!(result.is_ok());
        assert_eq!(queue.sendable_count(), 1);
        assert_eq!(queue.recvable_count(), 1);

        let mut buffer = [0u8; 4];
        let result = queue.recv(&mut buffer, 4, NO_WAITING);
        assert!(result.is_ok());
        assert_eq!(buffer, [3u8, 3u8, 3u8, 3u8]);
        assert_eq!(queue.sendable_count(), 2);
        assert_eq!(queue.recvable_count(), 0);
    }
}
