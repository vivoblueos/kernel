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

// LiveFor pattern is used when we want to track lifetimes of values accessed via pointers.
#[derive(Default)]
pub struct LiveFor<'a>(PhantomData<&'a ()>);

impl LiveFor<'_> {
    pub const fn new() -> Self {
        Self(PhantomData)
    }
}

// Similar to LiveFor, additionally contains a reference to a value.
// Borrow and BorrowMut have been used in [rust-std](https://doc.rust-lang.org/std/borrow/trait.BorrowMut.html),
// so we use Iou (I Owe U, aka, 借据) to name this struct.
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

impl<T> LifetimeDelegator<'_, T> {
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

    fn assign_val<'b>(f: &mut Foo, val: &'b mut i32) -> LiveFor<'b> {
        f.val = Some(NonNull::from_mut(val));
        LiveFor::default()
    }

    fn unassign_val<'b>(_d: LiveFor<'_>, f: &'b mut Foo) -> LiveFor<'b> {
        f.val = None;
        LiveFor::default()
    }

    // Demonstrate how LiveFor pattern works.
    fn operate_on_stack_val(f: &mut Foo) {
        let mut livefor;
        {
            let mut val = 42;
            livefor = assign_val(f, &mut val);
            assert!(f.val.is_some());
            assert_eq!(unsafe { f.val.unwrap().read() }, 42);
            // The program doesn't compile if the following stmt is omitted.
            livefor = unassign_val(livefor, f);
        }
        drop(livefor);
    }

    fn operate_on_external_val(f: &mut Foo, val: &mut i32) {
        let mut livefor;
        {
            livefor = assign_val(f, val);
            assert!(f.val.is_some());
            assert_eq!(unsafe { f.val.unwrap().read() }, 42);
            // We don't need to unassign_val here, since val is still alive.
        }
        drop(livefor);
    }

    #[test]
    fn test_stack_val() {
        let mut f = Foo::default();
        operate_on_stack_val(&mut f);
        let mut val = 42;
        operate_on_external_val(&mut f, &mut val);
    }
}
