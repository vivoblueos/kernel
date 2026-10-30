# Method delegation with less boilerplate

[![Build Status](https://github.com/kobzol/rust-delegate/workflows/Tests/badge.svg)](https://github.com/kobzol/rust-delegate/actions)
[![Crates.io](https://img.shields.io/crates/v/delegate.svg)](https://crates.io/crates/delegate)

This crate removes some boilerplate for structs that simply delegate some of
their methods to one or more of their fields.

It gives you the `delegate!` macro, which delegates method calls to selected
expressions (usually inner fields).

## Example:

A Stack data structure implemented using an inner Vec via delegation.

```rust
use delegate::delegate;

#[derive(Clone, Debug)]
struct Stack<T> {
    inner: Vec<T>,
}
impl<T> Stack<T> {
    pub fn new() -> Self <T> {
        Self { inner: vec![] }
    }

    delegate! {
        to self.inner {
            pub fn is_empty(&self) -> bool;
            pub fn push(&mut self, value: T);
            pub fn pop(&mut self) -> Option<T>;
            pub fn clear(&mut self);

            #[call(len)]
            pub fn size(&self) -> usize;

            #[call(last)]
            pub fn peek(&self) -> Option<&T>;

        }
    }
}
```

## Features

### Delegate to a method with a different name
```rust
struct Stack {
    inner: Vec<u32>
}
impl Stack {
    delegate! {
        to self.inner {
            #[call(push)]
            pub fn add(&mut self, value: u32);
        }
    }
}
```

### Use an arbitrary inner field expression
```rust
struct Wrapper {
    inner: Rc<RefCell<Vec<u32>>>
}
impl Wrapper {
    delegate! {
        to self.inner.deref().borrow_mut() {
            pub fn push(&mut self, val: u32);
        }
    }
}
```

### Delegate to enum variants
```rust
use delegate::delegate;

enum Enum {
    A(A),
    B(B),
    C { v: C },
}

struct A {
    val: usize,
}

impl A {
    fn dbg_inner(&self) -> usize {
        dbg!(self.val);
        1
    }
}
struct B {
    val_a: String,
}

impl B {
    fn dbg_inner(&self) -> usize {
        dbg!(self.val_a.clone());
        2
    }
}

struct C {
    val_c: f64,
}

impl C {
    fn dbg_inner(&self) -> usize {
        dbg!(self.val_c);
        3
    }
}

impl Enum {
    delegate! {
        // transformed to
        //
        // ```rust
        // match self {
        //     Enum::A(a) => a.dbg_inner(),
        //     Enum::B(b) => { println!("i am b"); b }.dbg_inner(),
        //     Enum::C { v: c } => { c }.dbg_inner(),
        // }
        // ```
        to match self {
            Enum::A(a) => a,
            Enum::B(b) => { println!("i am b"); b },
            Enum::C { v: c } => { c },
        } {
            fn dbg_inner(&self) -> usize;
        }
    }
}
```

### Use modifiers that alter the generated method body
```rust
use delegate::delegate;
struct Inner;
impl Inner {
    pub fn method(&self, num: u32) -> u32 { num }
    pub fn method_res(&self, num: u32) -> Result<u32, ()> { Ok(num) }
}
struct Wrapper {
    inner: Inner
}
impl Wrapper {
    delegate! {
        to self.inner {
            // calls method, converts result to u64 using `From`
            #[into]
            pub fn method(&self, num: u32) -> u64;

            // calls method, returns ()
            #[call(method)]
            pub fn method_noreturn(&self, num: u32);

            // calls method, converts result to i6 using `TryFrom`
            #[try_into]
            #[call(method)]
            pub fn method2(&self, num: u32) -> Result<u16, std::num::TryFromIntError>;

            // calls method_res, unwraps the result
            #[unwrap]
            pub fn method_res(&self, num: u32) -> u32;

            // calls method_res, unwraps the result, then calls into
            #[unwrap]
            #[into]
            #[call(method_res)]
            pub fn method_res_into(&self, num: u32) -> u64;

            // specify explicit type for into
            #[into(u64)]
            #[call(method)]
            pub fn method_into_explicit(&self, num: u32) -> u64;
        }
    }
}
```

### Custom called expression

The `#[expr()]` attribute can be used to modify the delegated call. You can use the `$` sigil as a placeholder for what delegate would normally expand to, and wrap that expression with custom code.

_Note:_ the `$` placeholder isn't required and can be present multiple times if you want.

```rust
struct A(Vec<u8>);

impl A {
    delegate! {
        to self.0 {
            #[expr(*$.unwrap())]
            /// Here `$` == `self.0.get(idx)`
            /// Will expand to `*self.0.get(idx).unwrap()`
            fn get(&self, idx: usize) -> u8;

            #[call(get)]
            #[expr($?.checked_pow(2))]
            /// Here `$` == `self.0.get(idx)`
            /// Will expand to `self.0.get(idx)?.checked_pow(2)`
            fn get_checked_pow_2(&self, idx: usize) -> Option<u8>;
        }
    }
}
```

### Add additional arguments to method
```rust
struct Inner(u32);
impl Inner {
    pub fn new(m: u32) -> Self {
        // some "very complex" constructing work
        Self(m)
    }
    pub fn method(&self, n: u32) -> u32 {
        self.0 + n
    }
}

struct Wrapper {
    inner: OnceCell<Inner>,
}

impl Wrapper {
    pub fn new() -> Self {
        Self {
            inner: OnceCell::new(),
        }
    }
    fn content(&self, val: u32) -> &Inner {
        self.inner.get_or_init(|| Inner(val))
    }
    delegate! {
        to |k: u32| self.content(k) {
            // `wrapper.method(k, num)` will call `self.content(k).method(num)`
            pub fn method(&self, num: u32) -> u32;
        }
    }
}
```

### Call `await` on async functions
```rust
struct Inner;
impl Inner {
    pub async fn method(&self, num: u32) -> u32 { num }
}
struct Wrapper {
    inner: Inner
}
impl Wrapper {
    delegate! {
        to self.inner {
            // calls method(num).await, returns impl Future<Output = u32>
            pub async fn method(&self, num: u32) -> u32;
            // calls method(num).await.into(), returns impl Future<Output = u64>
            #[into]
            #[call(method)]
            pub async fn method_into(&self, num: u32) -> u64;
        }
    }
}
```

You can use the `#[await(true/false)]` attribute on delegated methods to specify
if `.await` should be generated after the delegated expression. It will be
generated by default if the delegated method is `async`.

### Delegate to multiple fields
```rust
struct MultiStack {
    left: Vec<u32>,
    right: Vec<u32>,
}
impl MultiStack {
    delegate! {
        to self.left {
            /// Push an item to the top of the left stack
            #[call(push)]
            pub fn push_left(&mut self, value: u32);
        }
        to self.right {
            /// Push an item to the top of the right stack
            #[call(push)]
            pub fn push_right(&mut self, value: u32);
        }
    }
}
```

### Inline attributes
`rust-delegate` inserts `#[inline(always)]` automatically. You can override that decision by specifying `#[inline]`
manually on the delegated method.

### Segment attributes
You can use an attribute on a whole delegation segment to automatically apply it to all methods in that segment:

```rust
struct Wrapper {
    inner: Inner
}

impl Wrapper {
    delegate! {
   #[unwrap]
   to self.inner {
     fn foo(&self) -> u32; // calls self.inner.foo().unwrap()
     fn bar(&self) -> u32; // calls self.inner.bar().unwrap()
   }
 }
}
```

### Adding additional arguments
You can specify expressions in the signature that will be used as delegated arguments:

```rust
use delegate::delegate;

struct Inner;
impl Inner {
    pub fn polynomial(&self, a: i32, x: i32, b: i32, y: i32, c: i32) -> i32 {
        a + x * x + b * y + c
    }
}
struct Wrapper {
    inner: Inner,
    a: i32,
    b: i32,
    c: i32
}
impl Wrapper {
    delegate! {
        to self.inner {
            // Calls `polynomial` on `inner` with `self.a`, `self.b` and
            // `self.c` passed as arguments `a`, `b`, and `c`, effectively
            // calling `polynomial(self.a, x, self.b, y, self.c)`.
            pub fn polynomial(&self, [ self.a ], x: i32, [ self.b ], y: i32, [ self.c ]) -> i32 ;
            // Calls `polynomial` on `inner` with `0`s passed for arguments
            // `a` and `x`, and `self.b` and `self.c` for `b` and `c`,
            // effectively calling `polynomial(0, 0, self.b, y, self.c)`.
            #[call(polynomial)]
            pub fn linear(&self, [ 0 ], [ 0 ], [ self.b ], y: i32, [ self.c ]) -> i32 ;
        }
    }
}
```

### Parameter modifiers
You can modify how will an input parameter be passed to the delegated method with parameter attribute modifiers. Currently, the following modifiers are supported:
- `#[into]`: Calls `.into()` on the parameter passed to the delegated method.
- `#[as_ref]`: Calls `.as_ref()` on the parameter passed to the delegated method.
- `#[newtype]`: Accesses the first tuple element (`.0`) of the parameter passed to the delegated method.

> Note that these modifiers might be removed in the future, try to use the more general `#[expr]` mechanism to achieve this functionality.

```rust
use delegate::delegate;

struct InnerType {}
impl InnerType {
    fn foo(&self, other: Self) {}
}

impl From<Wrapper> for InnerType {
    fn from(wrapper: Wrapper) -> Self {
        wrapper.0
    }
}

struct Wrapper(InnerType);
impl Wrapper {
    delegate! {
        to self.0 {
            // Calls `self.0.foo(other.into());`
            pub fn foo(&self, #[into] other: Self);
            // Calls `self.0.bar(other.0);`
            pub fn bar(&self, #[newtype] other: Self);
        }
    }
}
```

### Delegate associated functions
```rust
use delegate::delegate;

struct A {}
impl A {
    fn foo(a: u32) -> u32 {
        a + 1
    }
}

struct B;

impl B {
    delegate! {
        to A {
            fn foo(a: u32) -> u32;
        }
    }
}

assert_eq!(B::foo(1), 2);
```

### Delegate associated constants
```rust
use delegate::delegate;

trait WithConst {
    const TOTO: u8;
}

struct A;
impl WithConst for A {
    const TOTO: u8 = 1;
}

struct B;
impl WithConst for B {
    const TOTO: u8 = 2;
}
struct C;
impl WithConst for C {
    const TOTO: u8 = 2;
}

enum Enum {
    A(A),
    B(B),
    C(C),
}

impl Enum {
    delegate! {
        to match self {
            Self::A(a) => a,
            Self::B(b) => b,
            Self::C(c) => { println!("hello from c"); c },
        } {
            #[const(WithConst::TOTO)]
            fn get_toto(&self) -> u8;
        }
    }
}

assert_eq!(Enum::A(A).get_toto(), <A as WithConst>::TOTO);
```

## License

Licensed under either of

- Apache License, Version 2.0, ([LICENSE-APACHE](LICENSE-APACHE) or
  http://www.apache.org/licenses/LICENSE-2.0)
- MIT license ([LICENSE-MIT](LICENSE-MIT) or http://opensource.org/licenses/MIT)

at your option.

## Contribution

Unless you explicitly state otherwise, any contribution intentionally submitted
for inclusion in the work by you, as defined in the Apache-2.0 license, shall be
dual licensed as above, without any additional terms or conditions.

## Conduct

Please follow the [Rust Code of Conduct]. For escalation or moderation issues
please contact the crate author(s) listed in [`Cargo.toml`](./Cargo.toml).

[Rust Code of Conduct]: https://www.rust-lang.org/conduct.html
