// Adopted from
// https://github.com/alexcrichton/dlmalloc-rs/blob/master/tests/global.rs
use std::collections::HashMap;

#[global_allocator]
#[cfg(any(all(target_arch = "wasm32", not(target_feature = "atomics")), unix))]
static A: rlsf::SmallGlobalTlsf = rlsf::SmallGlobalTlsf::new();

#[test]
fn foo() {
    println!("hello");
}

#[test]
fn map() {
    let mut m = HashMap::new();
    m.insert(1, 2);
    m.insert(5, 3);
    drop(m);
}

#[test]
fn strings() {
    // Format a string and throw it away
    _ = format!("foo, bar, {}", "baz");
}

#[cfg(not(target_arch = "wasm32"))]
#[test]
fn threads() {
    assert!(std::thread::spawn(|| panic!()).join().is_err());
}

#[test]
fn test_larger_than_word_alignment() {
    use std::mem;

    // Align to 32 bytes.
    #[repr(align(32))]
    struct Align32(u8);

    assert_eq!(mem::align_of::<Align32>(), 32);

    for _ in 0..1000 {
        let b = Box::new(Align32(42));

        let p = Box::into_raw(b);
        assert_eq!(p as usize % 32, 0, "{:p} should be aligned to 32", p);

        unsafe {
            let b = Box::from_raw(p);
            assert_eq!(b.0, 42);
        }
    }
}
