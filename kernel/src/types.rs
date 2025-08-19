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

use crate::sync::{ISpinLock, SpinLock, SpinLockGuard};
pub use blueos_infra::{
    impl_simple_intrusive_adapter,
    intrusive::Adapter as IntrusiveAdapter,
    list::{
        typed_atomic_ilist::AtomicListHead as AtomicIlistHead, typed_ilist::ListHead as IlistHead,
    },
    tinyarc::{
        TinyArc as Arc, TinyArcInner as ArcInner, TinyArcList as ArcList,
        TinyArcListIterator as ArcListIterator,
    },
    tinyrwlock::{IRwLock, RwLock, RwLockReadGuard, RwLockWriteGuard},
};
use core::marker::PhantomData;

#[cfg(target_pointer_width = "32")]
mod inner {
    pub type Uint = u8;
    pub type AtomicUint = core::sync::atomic::AtomicU8;
    pub type Int = i8;
    pub type AtomicInt = core::sync::atomic::AtomicI8;
}

#[cfg(target_pointer_width = "64")]
mod inner {
    pub type Uint = usize;
    pub type Int = isize;
    pub type AtomicUint = core::sync::atomic::AtomicUsize;
    pub type AtomicInt = core::sync::atomic::AtomicIsize;
}

#[cfg(target_pointer_width = "64")]
pub type ThreadPriority = u16;
#[cfg(target_pointer_width = "32")]
pub type ThreadPriority = u8;

pub use inner::*;

#[macro_export]
macro_rules! static_arc {
    ($name:ident($ty:ty, $val:expr),) => {
        #[allow(non_snake_case)]
        mod $name {
            use super::*;
            use $crate::types::{Arc, ArcInner};
            static CTRL_BLOCK: ArcInner<$ty> = ArcInner::const_new($val);
            pub(super) static PTR: Arc<$ty> = unsafe { Arc::const_new(&CTRL_BLOCK) };
        }
        use $name::PTR as $name;
    };
}

#[const_trait]
pub(crate) trait StaticListOwner<T, A: IntrusiveAdapter> {
    type List = ArcList<T, A>;
    fn get() -> &'static Arc<SpinLock<AtomicIlistHead<T, A>>>;
}

#[derive(Debug, Default)]
pub(crate) struct UniqueListHead<T, A: IntrusiveAdapter, O: StaticListOwner<T, A>>(
    AtomicIlistHead<T, A>,
    PhantomData<O>,
);

pub(crate) struct UniqueListHeadAccessGuard<
    T: 'static,
    A: IntrusiveAdapter + 'static,
    O: StaticListOwner<T, A>,
>(
    SpinLockGuard<'static, AtomicIlistHead<T, A>>,
    PhantomData<O>,
);

impl<T: 'static, A: IntrusiveAdapter + 'static, O: StaticListOwner<T, A>>
    UniqueListHeadAccessGuard<T, A, O>
{
    #[inline]
    pub fn new(w: SpinLockGuard<'static, AtomicIlistHead<T, A>>) -> Self {
        Self(w, PhantomData)
    }

    #[inline]
    pub fn detach(&mut self, me: &mut Arc<T>) -> bool {
        ArcList::<T, A>::detach(me)
    }

    #[inline]
    pub fn insert(&mut self, me: Arc<T>) -> bool {
        ArcList::<T, A>::insert_after(&mut *self.0, me)
    }

    #[inline]
    pub fn get_list_mut(&mut self) -> &mut AtomicIlistHead<T, A> {
        &mut self.0
    }

    #[inline]
    pub fn get_guard_mut(&mut self) -> &mut SpinLockGuard<'static, AtomicIlistHead<T, A>> {
        &mut self.0
    }
}

impl<T: 'static, A: IntrusiveAdapter + 'static, O: StaticListOwner<T, A>> UniqueListHead<T, A, O> {
    pub const fn new() -> Self {
        Self(AtomicIlistHead::<T, A>::new(), PhantomData)
    }

    #[inline]
    pub fn lock() -> UniqueListHeadAccessGuard<T, A, O> {
        let w = O::get().irqsave_lock();
        UniqueListHeadAccessGuard::new(w)
    }

    #[inline]
    pub fn detach(me: &mut Arc<T>) -> bool {
        let _guard = O::get().irqsave_lock();
        ArcList::<T, A>::detach(me)
    }

    #[inline]
    pub fn insert(me: Arc<T>) -> bool {
        let mut head = O::get().irqsave_lock();
        ArcList::<T, A>::insert_after(&mut *head, me)
    }
}

// FIXME: Enhance IntrusiveAdapter so that T's info is carried.
pub(crate) struct MutexToNode<T, Mutex: const IntrusiveAdapter, Node: const IntrusiveAdapter>(
    PhantomData<T>,
    PhantomData<Mutex>,
    PhantomData<Node>,
);

impl<T, Mutex: const IntrusiveAdapter, Node: const IntrusiveAdapter> const IntrusiveAdapter
    for MutexToNode<T, Mutex, Node>
{
    fn offset() -> usize {
        Mutex::offset() - Node::offset()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use blueos_test_macro::test;

    impl_simple_intrusive_adapter!(NodeOffset, Foobar, node);
    impl_simple_intrusive_adapter!(LockOffset, Foobar, node_lock);

    struct Foobar {
        node_lock: ISpinLock<
            AtomicIlistHead<Foobar, NodeOffset>,
            MutexToNode<Foobar, LockOffset, NodeOffset>,
        >,
        node: AtomicIlistHead<Foobar, NodeOffset>,
    }

    #[test]
    fn test_intrusive_mutex_arc_list_head() {
        type L = ArcList<Foobar, NodeOffset>;
    }

    #[test]
    fn test_intrusive_mutex_list_head() {
        type L = AtomicIlistHead<Foobar, NodeOffset>;
        let head = Arc::new(Foobar {
            node: AtomicIlistHead::new(),
            node_lock: ISpinLock::new(),
        });
        let a = Arc::new(Foobar {
            node: AtomicIlistHead::new(),
            node_lock: ISpinLock::new(),
        });
        let b = Arc::new(Foobar {
            node: AtomicIlistHead::new(),
            node_lock: ISpinLock::new(),
        });
        // For following insertions, the head doesn't get the share of ownership.
        let mut head_lock = head.node_lock.irqsave_lock();
        {
            let mut lock_a = a.node_lock.irqsave_lock();
            L::insert_after(&mut *head_lock, &mut *lock_a);
            drop(lock_a);
            assert_eq!(Arc::<Foobar>::strong_count(&a), 1);
        }
        {
            let mut lock_b = b.node_lock.irqsave_lock();
            L::insert_after(&mut *head_lock, &mut *lock_b);
        }
    }
}
