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

#[derive(Default)]
pub struct LifetimeDelegator<'a, T>(PhantomData<&'a T>);

impl<'a, T> LifetimeDelegator<'a, T> {
    pub const fn new() -> Self {
        LifetimeDelegator(PhantomData)
    }
}

// Borrow and BorrowMut have been used in [rust-std](https://doc.rust-lang.org/std/borrow/trait.BorrowMut.html),
// so we use Iou (I Owe You, aka, 借据) to name this struct.
#[derive(Default)]
#[repr(transparent)]
pub struct Iou<'a, T> {
    pub val: Option<&'a T>,
}

#[derive(Default)]
#[repr(transparent)]
pub struct IouMut<'a, T> {
    pub val: Option<&'a mut T>,
}

#[cfg(test)]
mod tests {
    use super::*;
    use core::ptr::NonNull;

    #[derive(Default)]
    struct Foo {
        val: Option<NonNull<i32>>,
    }

    fn assign_val<'a, 'b>(f: &'a mut Foo, val: &'b mut i32) -> LifetimeDelegator<'b, i32> {
        f.val = Some(NonNull::from_mut(val));
        LifetimeDelegator::default()
    }

    fn unassign_val<'a, 'b>(
        _d: LifetimeDelegator<'a, i32>,
        f: &'b mut Foo,
    ) -> LifetimeDelegator<'b, i32> {
        f.val = None;
        LifetimeDelegator::default()
    }

    fn operate_on_stack_val<'a>(f: &'a mut Foo) {
        let mut delegator;
        {
            let mut val = 42;
            delegator = assign_val(f, &mut val);
            assert!(f.val.is_some());
            assert_eq!(unsafe { f.val.unwrap().read() }, 42);
            // The program doesn't compile if the following stmt is omitted.
            delegator = unassign_val(delegator, f);
        }
        drop(delegator);
    }

    fn operate_on_external_val(f: &mut Foo, val: &mut i32) {
        let mut delegator;
        {
            delegator = assign_val(f, val);
            assert!(f.val.is_some());
            assert_eq!(unsafe { f.val.unwrap().read() }, 42);
            // We don't need to unassign_val here, since val is still alive.
        }
        drop(delegator);
    }

    #[test]
    fn test_stack_val() {
        let mut f = Foo::default();
        operate_on_stack_val(&mut f);
        let mut val = 42;
        operate_on_external_val(&mut f, &mut val);
    }
}
