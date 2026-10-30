// Purpose: This integration test checks that atomic_enum can be used in
// a no_std environment.

#![no_std]

use core::sync::atomic::Ordering;

use portable_atomic_enum::atomic_enum;

#[atomic_enum]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum FooBar {
    Foo,
    Bar,
}

#[test]
fn test_no_std_use() {
    let fb = AtomicFooBar::new(FooBar::Foo);
    let prev = fb
        .compare_exchange(
            FooBar::Foo,
            FooBar::Bar,
            Ordering::SeqCst,
            Ordering::Relaxed,
        )
        .unwrap();
    assert_eq!(prev, FooBar::Foo);

    let prev_fail = fb.compare_exchange(
        FooBar::Foo,
        FooBar::Bar,
        Ordering::SeqCst,
        Ordering::Relaxed,
    );
    assert!(prev_fail.is_err());
}
