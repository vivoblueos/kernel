# Kernel's basic data types

## Arc
A customized `Arc`(`infra/src/tinyarc.rs`), is implemented for
the kernel. Compared to `alloc::sync::Arc`, there is no much
difference, except it has only `strong_count` thus reduced its size
and is friendly to embedded devices. Also its memory layout is known
to `blueos_infra`, so our instrusive list can cooperate with it
easily.


## Intrusive list
`blueos_infra`'s ilist(`infra/src/list/typed_ilist.rs`) is typed and
unsafe. It's like C-style's ilist, however we recommend developers
not using it directly but with smart pointers. We implement `ArcList`
on top of the typed ilst with `Arc` mentioned above and guarantees safety.
