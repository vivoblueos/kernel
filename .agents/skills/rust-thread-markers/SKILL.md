---
name: rust-thread-markers
description: Use NotSend, NotSync, or NotThreadSafe fields when preventing a type from automatically implementing Send or Sync or when replacing existing handwritten negative implementations of either trait.
---

# Using thread markers to suppress automatic implementations

These three zero-sized types serve only to prevent Rust from automatically implementing the corresponding traits for a type that contains them.

| Required constraint | Field type      |
| ------------------- | --------------- |
| `!Send`             | `NotSend`       |
| `!Sync`             | `NotSync`       |
| Both                | `NotThreadSafe` |

Each marker type has a constant of the same name for use in field initializers.
This lets you write `_not_send: NotSend` in both the field declaration and the initializer, which reads more clearly than using `PhantomData` directly.

## Replacing handwritten negative implementations

Use the corresponding marker field to replace `impl !Send`, `impl !Sync`, or both.
Marker fields cannot override a handwritten positive implementation.
Avoid selecting a marker that suppresses automatic implementation of a trait the enclosing type explicitly implements.
This also applies to conditional implementations. With `unsafe impl<T: Sync> Sync for Foo<T>`, Rust does not fall back to field-based inference for `Foo<T>` when `T: Sync` is unsatisfied, so those cases need no extra marker.

Consider `Send` and `Sync` separately. If the enclosing type explicitly implements one trait and needs to suppress the other, choose a marker for the latter alone.
For example, if `Foo` has both `impl !Send` and `unsafe impl Sync`, replace `impl !Send` with a `NotSend` field and keep `unsafe impl Sync`. A `NotThreadSafe` field would also suppress automatic `Sync`.
