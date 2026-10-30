#![doc(html_root_url = "http://docs.rs/const-default/1.0.0")]
#![cfg_attr(not(feature = "std"), no_std)]
#![cfg_attr(feature = "unstable-docs", feature(doc_cfg))]
#![cfg_attr(
	all(feature = "unstable", feature = "alloc"),
	feature(const_btree_new)
)]
#![cfg_attr(feature = "unstable", feature(const_fn_trait_bound))]
#![cfg_attr(
	all(feature = "unstable", feature = "enable-atomics"),
	feature(cfg_target_has_atomic)
)]
#![cfg_attr(
	feature = "enable-atomics",
	allow(clippy::declare_interior_mutable_const)
)]

#[cfg(feature = "alloc")]
extern crate alloc;

#[cfg(feature = "derive")]
#[cfg_attr(feature = "unstable-docs", doc(cfg(feature = "derive")))]
pub use const_default_derive::ConstDefault;

/// Implements a compilation time default value for the implemented type.
///
/// # Note
///
/// Unlike the [`Default`] trait implementation the `DEFAULT` of implementations
/// of this trait can be used in constant evaluation contexts.
///
/// # Example
///
/// ```
/// # #[cfg(feature = "std")]
/// # const _: () = {
/// # use const_default::ConstDefault;
/// const VEC: Vec<u8> = <Vec<u8> as ConstDefault>::DEFAULT;
/// # };
/// ```
///
/// The above code works while the below code does not:
///
/// ```compile_fail
/// const VEC: Vec<u8> = <Vec<u8> as Default>::default();
/// ```
pub trait ConstDefault: Sized {
	/// The constant default value.
	const DEFAULT: Self;
}

/// Returns the compilation time default value for a type
#[inline]
#[cfg(feature = "unstable")]
#[cfg_attr(feature = "unstable-docs", doc(cfg(feature = "unstable")))]
pub const fn const_default<T: ConstDefault>() -> T {
	T::DEFAULT
}

impl<T> ConstDefault for Option<T> {
	const DEFAULT: Self = None;
}

#[cfg(feature = "alloc")]
#[cfg_attr(
	feature = "unstable-docs",
	doc(cfg(any(feature = "std", feature = "alloc")))
)]
impl<'a, T> ConstDefault for alloc::borrow::Cow<'a, T>
where
	T: alloc::borrow::ToOwned + ?Sized + 'a,
	<T as alloc::borrow::ToOwned>::Owned: ConstDefault,
{
	const DEFAULT: Self = Self::Owned(
		<<T as alloc::borrow::ToOwned>::Owned as ConstDefault>::DEFAULT,
	);
}

impl<T: ConstDefault> ConstDefault for core::cell::Cell<T> {
	const DEFAULT: Self = Self::new(T::DEFAULT);
}

impl<T: ConstDefault> ConstDefault for core::cell::UnsafeCell<T> {
	const DEFAULT: Self = Self::new(T::DEFAULT);
}

impl<T: ConstDefault> ConstDefault for core::cell::RefCell<T> {
	const DEFAULT: Self = Self::new(T::DEFAULT);
}

// TODO revisit whether this makes sense?
impl<T: ConstDefault> ConstDefault for core::mem::MaybeUninit<T> {
	const DEFAULT: Self = Self::new(T::DEFAULT);
}

#[cfg(feature = "alloc")]
#[cfg_attr(
	feature = "unstable-docs",
	doc(cfg(any(feature = "std", feature = "alloc")))
)]
impl<T> ConstDefault for alloc::vec::Vec<T> {
	const DEFAULT: Self = Self::new();
}

#[cfg(feature = "alloc")]
#[cfg_attr(
	feature = "unstable-docs",
	doc(cfg(any(feature = "std", feature = "alloc")))
)]
impl ConstDefault for alloc::string::String {
	const DEFAULT: Self = Self::new();
}

#[cfg(all(feature = "alloc", feature = "unstable"))]
#[cfg_attr(
	feature = "unstable-docs",
	doc(
		cfg(any(feature = "std", feature = "alloc")),
		cfg(feature = "unstable")
	)
)]
impl<K: Ord, V> ConstDefault for alloc::collections::BTreeMap<K, V> {
	const DEFAULT: Self = Self::new();
}

#[cfg(all(feature = "alloc", feature = "unstable"))]
#[cfg_attr(
	feature = "unstable-docs",
	doc(
		cfg(any(feature = "std", feature = "alloc")),
		cfg(feature = "unstable")
	)
)]
impl<T: Ord> ConstDefault for alloc::collections::BTreeSet<T> {
	const DEFAULT: Self = Self::new();
}

#[cfg(feature = "alloc")]
#[cfg_attr(
	feature = "unstable-docs",
	doc(cfg(any(feature = "std", feature = "alloc")))
)]
impl<T> ConstDefault for alloc::collections::LinkedList<T> {
	const DEFAULT: Self = Self::new();
}

impl<'a, T: 'a> ConstDefault for &'a [T] {
	const DEFAULT: Self = &[];
}

impl<T> ConstDefault for *const T {
	const DEFAULT: Self = core::ptr::null();
}

impl<T> ConstDefault for *mut T {
	const DEFAULT: Self = core::ptr::null_mut();
}

impl<T: ConstDefault> ConstDefault for core::mem::ManuallyDrop<T> {
	const DEFAULT: Self = Self::new(T::DEFAULT);
}

impl<T: ?Sized> ConstDefault for core::marker::PhantomData<T> {
	const DEFAULT: Self = Self;
}

impl ConstDefault for core::marker::PhantomPinned {
	const DEFAULT: Self = Self;
}

impl<T> ConstDefault for core::iter::Empty<T> {
	const DEFAULT: Self = core::iter::empty();
}

impl<T: ConstDefault> ConstDefault for core::num::Wrapping<T> {
	const DEFAULT: Self = Self(T::DEFAULT);
}

impl ConstDefault for core::time::Duration {
	const DEFAULT: Self = core::time::Duration::from_secs(0);
}

#[cfg(feature = "std")]
#[cfg_attr(feature = "unstable-docs", doc(cfg(feature = "std")))]
impl ConstDefault for std::sync::Once {
	const DEFAULT: Self = Self::new();
}

macro_rules! impl_num {
	($($ty:ty=$d:expr$(;$name:ident=$width:literal)?),*) => {
		$(
			impl ConstDefault for $ty {
				const DEFAULT: Self = $d;
			}

			impl ConstDefault for &$ty {
				const DEFAULT: Self = &<$ty as ConstDefault>::DEFAULT;
			}

			$(
				#[cfg(feature = "enable-atomics")]
				#[cfg_attr(feature = "unstable-docs", doc(cfg(any(feature = "default", feature = "enable-atomics"))))]
				#[cfg_attr(feature = "unstable", cfg(target_has_atomic = $width))]
				impl ConstDefault for core::sync::atomic::$name {
					const DEFAULT: Self = Self::new(ConstDefault::DEFAULT);
				}
			)?
		)*
	};
}

impl_num! {
	()=(), bool=false, f32=0.0, f64=0.0, char='\x00', &str="",
	u8=0;AtomicU8="8", u16=0;AtomicU16="16", u32=0;AtomicU32="32", u64=0;AtomicU64="64", usize=0;AtomicUsize="ptr",
	i8=0;AtomicI8="8", i16=0;AtomicI16="16", i32=0;AtomicI32="32", i64=0;AtomicI64="64", isize=0;AtomicIsize="ptr",
	i128=0, u128=0
}

#[cfg(feature = "enable-atomics")]
#[cfg_attr(
	feature = "unstable-docs",
	doc(cfg(any(feature = "default", feature = "enable-atomics")))
)]
#[cfg_attr(feature = "unstable", cfg(target_has_atomic = "8"))]
impl ConstDefault for core::sync::atomic::AtomicBool {
	const DEFAULT: Self = Self::new(ConstDefault::DEFAULT);
}

#[cfg(feature = "enable-atomics")]
#[cfg_attr(
	feature = "unstable-docs",
	doc(cfg(any(feature = "default", feature = "enable-atomics")))
)]
#[cfg_attr(feature = "unstable", cfg(target_has_atomic = "ptr"))]
impl<T> ConstDefault for core::sync::atomic::AtomicPtr<T> {
	const DEFAULT: Self = Self::new(core::ptr::null_mut());
}

macro_rules! impl_tuple {
	(@rec $t:ident) => { };
	(@rec $_:ident $($t:ident)+) => {
		impl_tuple! { @impl $($t)* }
		impl_tuple! { @rec $($t)* }
	};
	(@impl $($t:ident)*) => {
		impl<$($t: ConstDefault,)*> ConstDefault for ($($t,)*) {
			const DEFAULT: Self = ($($t::DEFAULT,)*);
		}
	};
	($($t:ident)*) => {
		impl_tuple! { @rec _t $($t)* }
	};
}

impl_tuple! {
	A B C D E F G H I J K L
}

impl<T: ConstDefault, const N: usize> ConstDefault for [T; N] {
	const DEFAULT: Self = [T::DEFAULT; N];
}
