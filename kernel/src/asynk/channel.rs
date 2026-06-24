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

//! Single-Producer Single-Consumer asynchronous channel.
//!
//! Provides a fixed-capacity lock-free ring-buffer channel with typed
//! `Sender` and `Receiver` halves for both async and synchronous use.
//!
//! # Integration with asynk
//!
//!     let (tx, rx) = channel::<Message, 16>();
//!     asynk::spawn(async move {
//!         tx.send(msg).await;
//!     });
//!     // rx can be used in another tasklet or via recv_blocking().
//!
//! # Memory model
//!
//! The channel uses two independent atomics (`head`/`tail`) for SPSC
//! coordination — the producer writes to a reserved slot, then bumps
//! `head`; the consumer reads from its slot, then bumps `tail`.
//! A third atomic (`notify`) serves as the futex-word for `atomic_wait`.

use crate::{
    sync::{
        atomic_wait::{self, atomic_wait, atomic_wake},
        SpinLock,
    },
    time::Tick,
};
use alloc::sync::Arc as AllocArc;
use core::{
    cell::UnsafeCell,
    future::Future,
    mem::MaybeUninit,
    pin::Pin,
    sync::atomic::{AtomicUsize, Ordering},
    task::{Context, Poll, Waker},
};

// ---------------------------------------------------------------------------
// Errors
// ---------------------------------------------------------------------------

/// Error: channel is full or disconnected.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct TrySendError<T>(pub T);

/// Error: channel is empty or disconnected.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct TryRecvError;

/// Error from the async `send` future.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SendError;

/// Error from the async `recv` future.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct RecvError;

// ---------------------------------------------------------------------------
// Internal ring buffer
// ---------------------------------------------------------------------------

/// A single slot in the ring buffer.
struct Slot<T> {
    val: UnsafeCell<MaybeUninit<T>>,
}

impl<T> Slot<T> {
    const fn new() -> Self {
        Self {
            val: UnsafeCell::new(MaybeUninit::uninit()),
        }
    }
}

// ---------------------------------------------------------------------------
// Shared channel state
// ---------------------------------------------------------------------------

/// Inner state shared between `Sender` and `Receiver`.
pub(crate) struct ChanInner<T, const N: usize> {
    /// Ring buffer slots.
    buf: [Slot<T>; N],
    /// Producer write index. Only the sender writes this.
    head: AtomicUsize,
    /// Consumer read index. Only the receiver writes this.
    tail: AtomicUsize,
    /// Notification counter: futex-word for atomic_wait/wake, and
    /// version stamp for waker comparison.
    notify: AtomicUsize,
    /// Waker stored by the sender when the buffer is full.
    send_waker: SpinLock<Option<Waker>>,
    /// Waker stored by the receiver when the buffer is empty.
    recv_waker: SpinLock<Option<Waker>>,
    /// Set to `true` when either half is dropped and wants to unblock
    /// the other.
    disconnected: AtomicUsize,
}

impl<T, const N: usize> core::fmt::Debug for ChanInner<T, N> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("ChanInner")
            .field("head", &self.head)
            .field("tail", &self.tail)
            .field("notify", &self.notify)
            .field("disconnected", &self.disconnected)
            .finish()
    }
}

unsafe impl<T: Send, const N: usize> Send for ChanInner<T, N> {}

// SAFETY: `ChanInner` is shared by exactly one `Sender` and one `Receiver`.
// The producer is the only writer of `head` and the only initializer of empty
// slots; the consumer is the only writer of `tail` and the only reader that
// moves initialized values out. The release/acquire ordering on `head` and
// `tail` publishes slot initialization before receive and slot reclamation
// before reuse. No shared references to `T` are ever exposed, so `T: Sync` is
// not required; `T: Send` is enough because values are transferred by ownership
// between execution contexts.
unsafe impl<T: Send, const N: usize> Sync for ChanInner<T, N> {}

impl<T, const N: usize> ChanInner<T, N> {
    const fn new() -> Self {
        const {
            assert!(N > 1, "AsyncChannel capacity must be at least 2");
            assert!(
                N.is_power_of_two(),
                "AsyncChannel capacity must be a power of two"
            );
        }
        Self {
            buf: [const { Slot::new() }; N],
            head: AtomicUsize::new(0),
            tail: AtomicUsize::new(0),
            notify: AtomicUsize::new(0),
            send_waker: SpinLock::new(None),
            recv_waker: SpinLock::new(None),
            disconnected: AtomicUsize::new(0),
        }
    }

    #[inline]
    fn mask(index: usize) -> usize {
        index & (N - 1)
    }

    #[inline]
    pub(crate) fn len(&self) -> usize {
        self.head
            .load(Ordering::Acquire)
            .wrapping_sub(self.tail.load(Ordering::Acquire))
    }

    #[inline]
    pub(crate) fn is_empty(&self) -> bool {
        let h = self.head.load(Ordering::Relaxed);
        let t = self.tail.load(Ordering::Relaxed);
        h == t
    }

    #[inline]
    pub(crate) fn is_full(&self) -> bool {
        self.len() >= N
    }

    /// Attempt a send. Returns `Err(val)` if full or already disconnected.
    ///
    /// A concurrent close is allowed to race with send. Once this function has
    /// observed the channel as connected and reserved space, it may still
    /// publish the value even if the other half disconnects before the `head`
    /// update. This keeps the SPSC fast path to atomic loads/stores only.
    /// Enforcing a stronger "no send succeeds after close starts" guarantee
    /// would require serializing send and close with a lock, folding the close
    /// bit into a CAS-updated queue state, or supporting rollback after a slot
    /// write; those options add fast-path synchronization cost and complicate
    /// slot ownership/drop handling.
    pub(crate) fn try_send(&self, val: T) -> Result<(), T> {
        if self.is_disconnected() {
            return Err(val);
        }
        let head = self.head.load(Ordering::Relaxed);
        let tail = self.tail.load(Ordering::Acquire);
        if head.wrapping_sub(tail) >= N {
            return Err(val);
        }
        // Slot reserved — write.
        unsafe {
            (*self.buf[Self::mask(head)].val.get()).write(val);
        }
        self.head.store(head.wrapping_add(1), Ordering::Release);

        // Wake consumer.
        self.notify.fetch_add(1, Ordering::Release);
        let _ = atomic_wake(&self.notify, usize::MAX);
        if let Some(w) = self.recv_waker.lock().take() {
            w.wake();
        }
        Ok(())
    }

    /// Attempt a recv. Returns `Err(())` if empty.
    pub(crate) fn try_recv(&self) -> Result<T, ()> {
        let tail = self.tail.load(Ordering::Relaxed);
        let head = self.head.load(Ordering::Acquire);
        if tail == head {
            return Err(());
        }
        let val = unsafe { (*self.buf[Self::mask(tail)].val.get()).assume_init_read() };
        self.tail.store(tail.wrapping_add(1), Ordering::Release);

        // Wake producer.
        self.notify.fetch_add(1, Ordering::Release);
        let _ = atomic_wake(&self.notify, usize::MAX);
        if let Some(w) = self.send_waker.lock().take() {
            w.wake();
        }
        Ok(val)
    }

    pub(crate) fn disconnect(&self) {
        if self.disconnected.swap(1, Ordering::Release) == 0 {
            self.notify.fetch_add(1, Ordering::Release);
            let _ = atomic_wake(&self.notify, usize::MAX);
            if let Some(w) = self.send_waker.lock().take() {
                w.wake();
            }
            if let Some(w) = self.recv_waker.lock().take() {
                w.wake();
            }
        }
    }

    pub(crate) fn is_disconnected(&self) -> bool {
        self.disconnected.load(Ordering::Acquire) != 0
    }
}

impl<T, const N: usize> Drop for ChanInner<T, N> {
    fn drop(&mut self) {
        let tail = self.tail.load(Ordering::Relaxed);
        let head = self.head.load(Ordering::Relaxed);
        let mut pos = tail;
        while pos != head {
            unsafe { (*self.buf[Self::mask(pos)].val.get()).assume_init_drop() };
            pos = pos.wrapping_add(1);
        }
    }
}

// ---------------------------------------------------------------------------
// Channel — the public wrapper with Sender / Receiver halves
// ---------------------------------------------------------------------------

/// A fixed-capacity SPSC channel.
///
/// Create one with [`channel()`] and split into [`Sender`] + [`Receiver`].
pub struct AsyncChannel<T, const N: usize> {
    inner: ChanInner<T, N>,
}

impl<T, const N: usize> AsyncChannel<T, N> {
    /// Create a new channel (not yet split).
    pub const fn new() -> Self {
        Self {
            inner: ChanInner::new(),
        }
    }

    /// Split into sender and receiver halves.
    pub fn split(self) -> (Sender<T, N>, Receiver<T, N>) {
        let inner = AllocArc::new(self.inner);
        (
            Sender {
                inner: inner.clone(),
            },
            Receiver { inner },
        )
    }
}

// ---------------------------------------------------------------------------
// Sender
// ---------------------------------------------------------------------------

/// The producing half of an `AsyncChannel`.
pub struct Sender<T, const N: usize> {
    inner: AllocArc<ChanInner<T, N>>,
}

impl<T, const N: usize> core::fmt::Debug for Sender<T, N> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("Sender").finish()
    }
}

impl<T, const N: usize> Sender<T, N> {
    /// Non-blocking send.
    pub fn try_send(&self, val: T) -> Result<(), TrySendError<T>> {
        self.inner.try_send(val).map_err(TrySendError)
    }

    /// Async send: await until space is available.
    pub fn send(&self, val: T) -> SendFuture<'_, T, N> {
        SendFuture {
            inner: &self.inner,
            item: MaybeUninit::new(val),
            done: false,
        }
    }

    /// Blocking send (via `atomic_wait`).
    pub fn send_blocking(&self, mut val: T) -> Result<(), SendError> {
        loop {
            if self.inner.is_disconnected() {
                return Err(SendError);
            }
            match self.inner.try_send(val) {
                Ok(()) => return Ok(()),
                Err(v) => {
                    let n = self.inner.notify.load(Ordering::Acquire);
                    if !self.inner.is_full() {
                        val = v;
                        continue;
                    }
                    if self.inner.is_disconnected() {
                        return Err(SendError);
                    }
                    atomic_wait(&self.inner.notify, n, Tick::MAX);
                    val = v;
                }
            }
        }
    }

    /// Close the channel from the sender side.
    pub fn close(&self) {
        self.inner.disconnect();
    }
}

impl<T, const N: usize> Drop for Sender<T, N> {
    fn drop(&mut self) {
        self.inner.disconnect();
    }
}

// ---------------------------------------------------------------------------
// Receiver
// ---------------------------------------------------------------------------

/// The consuming half of an `AsyncChannel`.
pub struct Receiver<T, const N: usize> {
    inner: AllocArc<ChanInner<T, N>>,
}

impl<T, const N: usize> core::fmt::Debug for Receiver<T, N> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("Receiver").finish()
    }
}

impl<T, const N: usize> Receiver<T, N> {
    /// Non-blocking recv.
    pub fn try_recv(&self) -> Result<T, TryRecvError> {
        self.inner.try_recv().map_err(|()| TryRecvError)
    }

    /// Async recv: await until data is available.
    pub fn recv(&self) -> RecvFuture<'_, T, N> {
        RecvFuture { inner: &self.inner }
    }

    /// Blocking recv (via `atomic_wait`).
    pub fn recv_blocking(&self) -> Result<T, RecvError> {
        loop {
            if self.inner.is_disconnected() && self.inner.is_empty() {
                return Err(RecvError);
            }
            match self.inner.try_recv() {
                Ok(val) => return Ok(val),
                Err(()) => {
                    let n = self.inner.notify.load(Ordering::Acquire);
                    if !self.inner.is_empty() {
                        continue;
                    }
                    if self.inner.is_disconnected() {
                        return Err(RecvError);
                    }
                    atomic_wait(&self.inner.notify, n, Tick::MAX);
                }
            }
        }
    }

    /// Close the channel from the receiver side.
    pub fn close(&self) {
        self.inner.disconnect();
    }
}

impl<T, const N: usize> Drop for Receiver<T, N> {
    fn drop(&mut self) {
        self.inner.disconnect();
    }
}

// ---------------------------------------------------------------------------
// SendFuture
// ---------------------------------------------------------------------------

/// Future yielded by [`Sender::send`].
#[must_use = "futures do nothing unless polled"]
pub struct SendFuture<'a, T, const N: usize> {
    inner: &'a ChanInner<T, N>,
    item: MaybeUninit<T>,
    done: bool,
}

impl<T, const N: usize> Future for SendFuture<'_, T, N> {
    type Output = Result<(), SendError>;

    fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
        let this = unsafe { self.get_unchecked_mut() };
        if this.done {
            return Poll::Ready(Ok(()));
        }
        if this.inner.is_disconnected() {
            unsafe { this.item.assume_init_drop() };
            this.done = true;
            return Poll::Ready(Err(SendError));
        }
        let val = unsafe { this.item.assume_init_read() };
        match this.inner.try_send(val) {
            Ok(()) => {
                this.done = true;
                Poll::Ready(Ok(()))
            }
            Err(val) => {
                this.item.write(val);
                *this.inner.send_waker.lock() = Some(cx.waker().clone());

                if this.inner.is_disconnected() {
                    this.inner.send_waker.lock().take();
                    unsafe { this.item.assume_init_drop() };
                    this.done = true;
                    return Poll::Ready(Err(SendError));
                }

                let val = unsafe { this.item.assume_init_read() };
                match this.inner.try_send(val) {
                    Ok(()) => {
                        this.inner.send_waker.lock().take();
                        this.done = true;
                        Poll::Ready(Ok(()))
                    }
                    Err(val) => {
                        this.item.write(val);
                        if this.inner.is_disconnected() {
                            this.inner.send_waker.lock().take();
                            unsafe { this.item.assume_init_drop() };
                            this.done = true;
                            Poll::Ready(Err(SendError))
                        } else {
                            Poll::Pending
                        }
                    }
                }
            }
        }
    }
}

impl<T, const N: usize> Drop for SendFuture<'_, T, N> {
    fn drop(&mut self) {
        if !self.done {
            unsafe { self.item.assume_init_drop() };
        }
    }
}

// ---------------------------------------------------------------------------
// RecvFuture
// ---------------------------------------------------------------------------

/// Future yielded by [`Receiver::recv`].
#[must_use = "futures do nothing unless polled"]
pub struct RecvFuture<'a, T, const N: usize> {
    inner: &'a ChanInner<T, N>,
}

impl<T, const N: usize> Future for RecvFuture<'_, T, N> {
    type Output = Result<T, RecvError>;

    fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
        if self.inner.is_disconnected() && self.inner.is_empty() {
            return Poll::Ready(Err(RecvError));
        }
        match self.inner.try_recv() {
            Ok(val) => Poll::Ready(Ok(val)),
            Err(()) => {
                // Buffer empty — register waker.
                *self.inner.recv_waker.lock() = Some(cx.waker().clone());
                // Re-check to avoid lost wakeup.
                match self.inner.try_recv() {
                    Ok(val) => {
                        // Waker was stored but we got data — clean up.
                        self.inner.recv_waker.lock().take();
                        Poll::Ready(Ok(val))
                    }
                    Err(()) => {
                        if self.inner.is_disconnected() && self.inner.is_empty() {
                            Poll::Ready(Err(RecvError))
                        } else {
                            Poll::Pending
                        }
                    }
                }
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Constructor
// ---------------------------------------------------------------------------

/// Create a new SPSC channel and split into `(Sender, Receiver)`.
pub fn channel<T, const N: usize>() -> (Sender<T, N>, Receiver<T, N>) {
    AsyncChannel::new().split()
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use blueos_test_macro::test;

    use crate::asynk;

    use super::*;

    /// Non-blocking try_send / try_recv, verify every received value.
    #[test]
    fn test_try_send_recv() {
        const CAP: usize = 4;
        let (tx, rx) = channel::<u32, CAP>();

        for i in 0..CAP {
            assert!(tx.try_send(i as u32).is_ok());
        }
        assert!(tx.try_send(99).is_err());

        for i in 0..CAP {
            let v = rx.try_recv().unwrap();
            assert_eq!(v, i as u32);
        }
        assert!(rx.try_recv().is_err());
    }

    /// Blocking send/recv, verify every value.
    #[test]
    fn test_send_blocking_recv_blocking() {
        const CAP: usize = 8;
        let (tx, rx) = channel::<u64, CAP>();

        for i in 0..CAP {
            tx.send_blocking(i as u64).unwrap();
        }
        for i in 0..CAP {
            let v = rx.recv_blocking().unwrap();
            assert_eq!(v, i as u64);
        }
    }

    /// Drop sender: receiver can drain remaining items, then gets error.
    #[test]
    fn test_disconnect_sender() {
        let (tx, rx) = channel::<u32, 4>();
        tx.try_send(10).unwrap();
        tx.try_send(20).unwrap();

        drop(tx);

        assert_eq!(rx.recv_blocking().unwrap(), 10);
        assert_eq!(rx.recv_blocking().unwrap(), 20);
        assert!(rx.recv_blocking().is_err());
        assert!(rx.try_recv().is_err());
    }

    /// Drop receiver: sender gets error.
    #[test]
    fn test_disconnect_receiver() {
        let (tx, rx) = channel::<u32, 4>();
        drop(rx);
        assert!(tx.send_blocking(42).is_err());
        assert!(tx.try_send(42).is_err());
    }

    /// Async send/recv via block_on, verify every value.
    #[test]
    fn test_async_send_recv() {
        const CAP: usize = 4;
        let (tx, rx) = channel::<u32, CAP>();

        for i in 0..CAP {
            tx.send_blocking(i as u32).unwrap();
        }

        asynk::block_on(async move {
            let v0 = rx.recv().await.unwrap();
            assert_eq!(v0, 0);
            tx.send(v0).await.unwrap();

            let v1 = rx.recv().await.unwrap();
            assert_eq!(v1, 1);
            let v2 = rx.recv().await.unwrap();
            assert_eq!(v2, 2);
            let v3 = rx.recv().await.unwrap();
            assert_eq!(v3, 3);
            let v0_back = rx.recv().await.unwrap();
            assert_eq!(v0_back, 0);
        });
    }

    /// Async recv after sender drops.
    #[test]
    fn test_async_disconnect() {
        let (tx, rx) = channel::<u32, 4>();
        tx.send_blocking(100).unwrap();
        tx.send_blocking(200).unwrap();
        drop(tx);

        asynk::block_on(async move {
            let v1 = rx.recv().await.unwrap();
            assert_eq!(v1, 100);
            let v2 = rx.recv().await.unwrap();
            assert_eq!(v2, 200);
            assert!(rx.recv().await.is_err());
        });
    }

    /// Explicit close via sender.
    #[test]
    fn test_sender_close() {
        let (tx, rx) = channel::<u32, 4>();
        tx.try_send(77).unwrap();
        tx.close();

        assert_eq!(rx.recv_blocking().unwrap(), 77);
        assert!(rx.recv_blocking().is_err());
        assert!(tx.send_blocking(88).is_err());
    }

    /// Explicit close via receiver.
    #[test]
    fn test_receiver_close() {
        let (tx, rx) = channel::<u32, 4>();
        rx.close();
        assert!(tx.send_blocking(99).is_err());
    }

    /// Ring-buffer wrap-around: multiple fill-drain cycles.
    #[test]
    fn test_wrap_around() {
        const CAP: usize = 4;
        let (tx, rx) = channel::<i32, CAP>();

        for cycle in 0..8 {
            for i in 0..CAP {
                tx.send_blocking((cycle * CAP + i) as i32).unwrap();
            }
            for i in 0..CAP {
                let v = rx.recv_blocking().unwrap();
                assert_eq!(v, (cycle * CAP + i) as i32);
            }
        }
    }

    /// After disconnect, try_send returns the original value.
    #[test]
    fn test_send_after_disconnect() {
        let (tx, rx) = channel::<u32, 4>();
        drop(rx);

        let err = tx.try_send(7).unwrap_err();
        assert_eq!(err.0, 7);
        assert!(tx.send_blocking(8).is_err());
    }
}
