---
name: rust-raw-pointer-idioms
description: "Use when writing or reviewing Rust raw pointer creation, field projections, and intrusive container code. Apply the semantics of &raw to distinguish removing intermediate references from simplifying conversion expressions."
---

# Understanding Raw Pointer Creation Through &raw

When using this skill, first determine whether the code only needs a raw pointer, then decide whether a reference should be created. Prioritize removing unnecessary reference creation, and improve expression clarity where there is a clear benefit.

## Why &raw Exists

Rust references carry more than a location: they require the referenced data to satisfy alignment, validity, and aliasing constraints. Consequently, `&value as *const T` first creates a reference and then converts it to a raw pointer. The conversion does not undo the requirements imposed when the reference was created. For potentially unaligned packed fields, uninitialized data, or linked nodes where a temporary exclusive borrow is inappropriate, this intermediate step can be the source of the problem.

Rust first stabilized `addr_of!` and `addr_of_mut!` in [1.51.0 (2021-03-25)](https://blog.rust-lang.org/2021/03/25/Rust-1.51.0/), allowing raw pointers to be constructed without going through references. It later stabilized the native syntax `&raw const` and `&raw mut` in [1.82.0 (2024-10-17)](https://blog.rust-lang.org/2024/10/17/Rust-1.82.0/#native-syntax-for-creating-a-raw-pointer), corresponding to those two macros. The native syntax expresses "construct a raw pointer from a place" more directly; replacing a macro with its corresponding syntax does not itself improve safety.

This gives two distinct benefits: replacing reference creation followed by a cast with direct raw pointer creation avoids that reference, while expressing existing macros or lengthy conversions more directly primarily improves readability. Distinguish these benefits when evaluating and reporting changes.

## What It Does and Which Constraints Remain

`&raw const place` produces `*const T`, and `&raw mut place` produces `*mut T`. The operand is treated as a place expression. The operation itself neither reads nor writes the value at that place, nor creates a reference to the final place. Function calls, dereferences, or indexing needed to compute the place still occur. [Semantics](https://doc.rust-lang.org/reference/expressions/operator-expr.html#raw-borrow-operators)

```rust
let mut value = 7_u32;
let p = &raw const value;
let q = &raw mut value;

let r = &value;
let same_target = &raw const *r; // Points to value.
let reference_slot = &raw const r; // Points to the reference variable r itself.
```

Always confirm the operand's type. Values, existing references, raw pointers, and smart pointers cannot be handled by the same textual replacement rule. Preserve the original expression's evaluation count, pointer target, source mutability, and wide pointer metadata; pay particular attention to type inference and deref coercions in the original expression.

`&raw` grants no additional memory access permissions. Constructing a pointer and using it are separate steps: field projections must still remain within the required object bounds, and subsequent reads and writes must still satisfy alignment, initialization, lifetime, and aliasing constraints. Converting a pointer derived from a shared reference to `*mut T` does not make otherwise forbidden writes valid. Raw pointers also retain provenance and should not be understood solely as integer addresses. [Projection and permission constraints](https://doc.rust-lang.org/core/ptr/macro.addr_of.html)

## Where It Is Most Useful

Use `&raw` directly when a place can be described by a raw pointer but is unsuitable for creating a Rust reference. Typical cases include packed fields, initializing individual fields through `MaybeUninit`, and obtaining field pointers from an existing raw pointer. For example, consider a packed field:

```rust
#[repr(C, packed)]
struct Header {
    tag: u8,
    length: u32,
}

let header = Header { tag: 1, length: 8 };
// Avoid creating a potentially unaligned &header.length.
let length_ptr = &raw const header.length;
let length = unsafe { length_ptr.read_unaligned() };
```

Here, `&raw` addresses the reference creation problem when obtaining the pointer, while `read_unaligned()` addresses alignment during the subsequent read. The same distinction applies to uninitialized data: obtaining a raw pointer for initialization does not mean the uninitialized value may be read first.

Ordinary initialized objects can also use `&raw`. When a reference is created solely to be immediately converted into a raw pointer, prefer `&raw` directly. This applies to both explicit casts (`&value as *const T`, `&mut value as *mut T`) and implicit coercions (`let p: *const T = &value`). Use `&raw const value` or `&raw mut value` to express the intent without the intermediate reference. This is a clarity and reference-creation preference, not a claim of better performance.

Converting an existing reference does not require the same rewrite. For `r: &T`, both `let p: *const T = r` and `&raw const *r` can express the conversion; the latter does not eliminate the reference that already exists. Preserve clear conversions such as `ptr::from_ref(r)`, `ptr::from_mut(r)`, and `NonNull::from_ref(r)` or `NonNull::from_mut(r)`. Do not introduce `unsafe { NonNull::new_unchecked(...) }` merely to make such conversions use `&raw`. Whether the reference is used afterward is not the deciding factor; whether it was created solely for this conversion is.
