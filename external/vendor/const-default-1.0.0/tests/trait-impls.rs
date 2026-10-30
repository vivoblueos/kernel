use const_default::ConstDefault;
#[cfg(feature = "enable-atomics")]
use core::sync::atomic::{
	AtomicBool,
	AtomicI16,
	AtomicI32,
	AtomicI64,
	AtomicI8,
	AtomicIsize,
	AtomicPtr,
	AtomicU16,
	AtomicU32,
	AtomicU64,
	AtomicU8,
	AtomicUsize,
	Ordering,
};
use core::{
	cell::{Cell, RefCell},
	fmt::Debug,
};

/// Checks if both `ConstDefault` and `Default` implementations yield the same outcome.
fn compare_default_impls<T>()
where
	T: ConstDefault + Default + PartialEq + Debug,
{
	assert_eq!(<T as ConstDefault>::DEFAULT, <T as Default>::default());
}

macro_rules! compare_default_impls_for {
	( $( $ty:ty ),* $(,)? ) => {{
		$(
			compare_default_impls::<$ty>();
		)*
	}};
}

#[test]
fn primitive_impls_work() {
	#[rustfmt::skip]
	compare_default_impls_for!(
		bool, char,
		i8, i16, i32, i64, i128, isize,
		u8, u16, u32, u64, u128, usize,
	);
}

#[test]
fn tuple_impls_work() {
	#[rustfmt::skip]
	compare_default_impls_for!(
		(),
		(i8,),
		(i8, i16),
		(i8, i16, i32),
		(i8, i16, i32, i64),
		(i8, i16, i32, i64, i128),
		(i8, i16, i32, i64, i128, isize),
		(i8, i16, i32, i64, i128, isize, u8),
		(i8, i16, i32, i64, i128, isize, u8, u16),
		(i8, i16, i32, i64, i128, isize, u8, u16, u32),
		(i8, i16, i32, i64, i128, isize, u8, u16, u32, u64),
		(i8, i16, i32, i64, i128, isize, u8, u16, u32, u64, u128),
		(i8, i16, i32, i64, i128, isize, u8, u16, u32, u64, u128, usize),
	);
}

macro_rules! compare_default_impls_for_arrays {
	( $( $n:literal ),* $(,)? ) => {{
		$(
			compare_default_impls::<[(); $n]>();
		)*
	}};
}

#[test]
fn array_impls_work() {
	#[rustfmt::skip]
	compare_default_impls_for_arrays!(
		0, 1, 2, 3, 4, 5, 6, 7, 8, 9,
		10, 11, 12, 13, 14, 15, 16, 17, 18, 19,
		20, 21, 22, 23, 24, 25, 26, 27, 28, 29,
		30, 31, 32,
	);
}

#[cfg(feature = "enable-atomics")]
macro_rules! compare_default_impls_for_atomics {
	( $( $atomic_type:ty ),* $(,)? ) => {{
		$(
			assert_eq!(
				<$atomic_type as ConstDefault>::DEFAULT.load(Ordering::SeqCst),
				<$atomic_type as Default>::default().load(Ordering::SeqCst),
			);
		)*
	}};
}

#[test]
#[cfg(feature = "enable-atomics")]
fn atomic_impls_work() {
	compare_default_impls_for_atomics!(
		AtomicBool,
		AtomicI16,
		AtomicI32,
		AtomicI64,
		AtomicI8,
		AtomicIsize,
		AtomicU16,
		AtomicU32,
		AtomicU64,
		AtomicU8,
		AtomicUsize,
	);
	assert_eq!(
		<AtomicPtr<()> as ConstDefault>::DEFAULT.load(Ordering::SeqCst),
		<AtomicPtr<()> as Default>::default().load(Ordering::SeqCst),
	);
}

macro_rules! compare_default_impls_for_cells {
	( $( $cell_type:ty ),* $(,)? ) => {{
		$(
			assert_eq!(
				<$cell_type as ConstDefault>::DEFAULT.into_inner(),
				<$cell_type as Default>::default().into_inner(),
			);
		)*
	}};
}

#[test]
fn cell_impls_work() {
	#[rustfmt::skip]
	compare_default_impls_for_cells!(
		Cell<u8>,
		Cell<(u8, u16, u32)>,
		Cell<Cell<u8>>,
		RefCell<u8>,
		RefCell<(u8, u16, u32)>,
		RefCell<RefCell<u8>>,
	);
}
