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

use core::marker::PhantomData;

#[const_trait]
pub trait Adapter<T> {
    fn offset() -> usize;
}

#[macro_export]
macro_rules! impl_simple_intrusive_adapter {
    ($name:ident, $ty:ty, $($fields:expr)+) => {
        #[derive(Default, Debug)]
        pub struct $name;
        impl const $crate::intrusive::Adapter<$ty> for $name {
            fn offset() -> usize {
                core::mem::offset_of!($ty, $($fields)+)
            }
        }
    }
}

// This adapter is used when T has a field which has `From` adapter, the other
// field which has `To` adapter. Now we have a reference to the field owns the `From` adapter,
// we use this adapter to access the field owns the `To` adapter.
pub struct Relative<T, From: const Adapter<T>, To: const Adapter<T>, S>(
    PhantomData<T>,
    PhantomData<From>,
    PhantomData<To>,
    PhantomData<S>,
);

impl<T, From: const Adapter<T>, To: const Adapter<T>, S> const Adapter<S>
    for Relative<T, From, To, S>
{
    fn offset() -> usize {
        To::offset() - From::offset()
    }
}
