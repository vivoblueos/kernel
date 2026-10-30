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
//
// This code is based on relibc (original license follows):
// https://github.com/redox-os/relibc/blob/master/LICENSE
// standard MIT license

use core::{
    ffi::c_int,
    sync::atomic::{AtomicUsize, Ordering},
};

use libc::{
    timespec, EAGAIN, EBUSY, EDEADLK, EINVAL, EPERM, ETIMEDOUT, PTHREAD_MUTEX_DEFAULT,
    PTHREAD_MUTEX_ERRORCHECK, PTHREAD_MUTEX_NORMAL, PTHREAD_MUTEX_RECURSIVE, PTHREAD_MUTEX_ROBUST,
    PTHREAD_MUTEX_STALLED, PTHREAD_PRIO_NONE, PTHREAD_PROCESS_PRIVATE,
};

use super::FutexWaitResult;

#[repr(u8)]
#[derive(PartialEq)]
enum Ty {
    // The only difference between PTHREAD_MUTEX_NORMAL and PTHREAD_MUTEX_DEFAULT appears to be
    // that "normal" mutexes deadlock if locked multiple times on the same thread, whereas
    // "default" mutexes are UB in that case. So we can treat them as being the same type.
    Normal,
    Def,
    Errck,
    Recursive,
}

pub struct Mutex {
    // Actual locking word.
    inner: AtomicUsize,
    recursive_count: AtomicUsize,
    ty: Ty,
    robust: bool,
}

const STATE_UNLOCKED: usize = 0;
const WAITING_BIT: usize = 1 << 31;
const INDEX_MASK: usize = !WAITING_BIT;

// TODO: Lower limit is probably better.
const RECURSIVE_COUNT_MAX_INCLUSIVE: usize = usize::MAX;
// TODO: How many spins should we do before it becomes more time-economical to enter kernel mode
// via futexes?
// const SPIN_COUNT: usize = 0;

impl Mutex {
    #[allow(unreachable_patterns)]
    pub(crate) fn new(attr: &MutexAttr) -> Result<Self, c_int> {
        let MutexAttr {
            prioceiling: _,
            protocol: _,
            pshared: _,
            robust,
            ty,
        } = *attr;

        Ok(Self {
            inner: AtomicUsize::new(STATE_UNLOCKED),
            recursive_count: AtomicUsize::new(0),
            robust: match robust {
                PTHREAD_MUTEX_STALLED => false,
                PTHREAD_MUTEX_ROBUST => true,
                _ => return Err(EINVAL),
            },
            ty: match ty {
                PTHREAD_MUTEX_DEFAULT => Ty::Def,
                PTHREAD_MUTEX_ERRORCHECK => Ty::Errck,
                PTHREAD_MUTEX_RECURSIVE => Ty::Recursive,
                PTHREAD_MUTEX_NORMAL => Ty::Normal,
                _ => return Err(EINVAL),
            },
        })
    }

    pub fn prioceiling(&self) -> Result<c_int, c_int> {
        todo!()
    }

    pub fn replace_prioceiling(&self, _: c_int) -> Result<c_int, c_int> {
        todo!()
    }

    pub fn make_consistent(&self) -> Result<(), c_int> {
        todo!()
    }

    fn lock_inner(&self, deadline: Option<&timespec>) -> Result<(), c_int> {
        let this_thread = crate::pthread::pthread_self();

        loop {
            let result = self.inner.compare_exchange_weak(
                STATE_UNLOCKED,
                this_thread.try_into().unwrap(),
                Ordering::Acquire,
                Ordering::Relaxed,
            );

            match result {
                // CAS succeeded
                Ok(_) => {
                    if self.ty == Ty::Recursive {
                        self.increment_recursive_count()?;
                    }
                    return Ok(());
                }
                // CAS failed, but the mutex was recursive and we already own the lock.
                Err(thread)
                    if thread & INDEX_MASK == this_thread.try_into().unwrap()
                        && self.ty == Ty::Recursive =>
                {
                    self.increment_recursive_count()?;
                    return Ok(());
                }
                // CAS failed, but the mutex was error-checking and we already own the lock.
                Err(thread)
                    if thread & INDEX_MASK == this_thread.try_into().unwrap()
                        && self.ty == Ty::Errck =>
                {
                    return Err(EAGAIN);
                }
                // CAS spuriously failed, simply retry the CAS. TODO: Use core::hint::spin_loop()?
                Err(thread) if thread & INDEX_MASK == 0 => {
                    continue;
                }
                // CAS failed because some other thread owned the lock. We must now wait.
                Err(thread) => {
                    // If the mutex is not robust, simply futex_wait until unblocked.
                    if crate::sync::futex_wait(&self.inner, thread, deadline)
                        == FutexWaitResult::TimedOut as i32
                    {
                        return Err(ETIMEDOUT);
                    }
                }
            }
        }
    }

    pub fn lock(&self) -> Result<(), c_int> {
        self.lock_inner(None)
    }

    pub fn lock_with_timeout(&self, deadline: &timespec) -> Result<(), c_int> {
        self.lock_inner(Some(deadline))
    }

    fn increment_recursive_count(&self) -> Result<(), c_int> {
        // We don't have to worry about asynchronous signals here, since pthread_mutex_trylock
        // is not async-signal-safe.
        //
        // TODO: Maybe just use Cell? Send/Sync doesn't matter much anyway, and will be
        // protected by the lock itself anyway.

        let prev_recursive_count = self.recursive_count.load(Ordering::Relaxed);

        if prev_recursive_count == RECURSIVE_COUNT_MAX_INCLUSIVE {
            return Err(EAGAIN);
        }

        self.recursive_count
            .store(prev_recursive_count + 1, Ordering::Relaxed);

        Ok(())
    }

    pub fn try_lock(&self) -> Result<(), c_int> {
        let this_thread = crate::pthread::pthread_self();

        // TODO: If recursive, omitting CAS may be faster if it is already owned by this thread.
        let result = self.inner.compare_exchange(
            STATE_UNLOCKED,
            this_thread.try_into().unwrap(),
            Ordering::Acquire,
            Ordering::Relaxed,
        );

        if self.ty == Ty::Recursive {
            match result {
                Err(index) if index & INDEX_MASK != this_thread.try_into().unwrap() => {
                    return Err(EBUSY)
                }
                _ => (),
            }

            self.increment_recursive_count()?;

            return Ok(());
        }

        match result {
            Ok(_) => Ok(()),
            Err(index)
                if index & INDEX_MASK == this_thread.try_into().unwrap()
                    && self.ty == Ty::Errck =>
            {
                Err(EDEADLK)
            }
            Err(_) => Err(EBUSY),
        }
    }

    // Safe because we are not protecting any data.
    pub fn unlock(&self) -> Result<(), c_int> {
        if self.robust || matches!(self.ty, Ty::Recursive | Ty::Errck) {
            if self.inner.load(Ordering::Relaxed) & INDEX_MASK
                != crate::pthread::pthread_self().try_into().unwrap()
            {
                return Err(EPERM);
            }

            // TODO: Is this fence correct?
            core::sync::atomic::fence(Ordering::Acquire);
        }

        if self.ty == Ty::Recursive {
            let next = self.recursive_count.load(Ordering::Relaxed) - 1;
            self.recursive_count.store(next, Ordering::Relaxed);

            if next > 0 {
                return Ok(());
            }
        }

        self.inner.store(STATE_UNLOCKED, Ordering::Release);
        crate::sync::futex_wake(&self.inner, usize::MAX);

        Ok(())
    }
}

#[repr(C)]
#[derive(Clone, Copy)]
pub struct MutexAttr {
    pub prioceiling: c_int,
    pub protocol: c_int,
    pub pshared: c_int,
    pub robust: c_int,
    pub ty: c_int,
}

impl Default for MutexAttr {
    fn default() -> Self {
        Self {
            robust: PTHREAD_MUTEX_STALLED,
            pshared: PTHREAD_PROCESS_PRIVATE,
            protocol: PTHREAD_PRIO_NONE,
            prioceiling: 0,
            ty: PTHREAD_MUTEX_DEFAULT,
        }
    }
}
