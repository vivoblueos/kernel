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

/// Convert C string to byte array, stopping at first null byte or reaching max_len
pub fn c_name_to_bytes<const LEN: usize>(name_ptr: *const core::ffi::c_char) -> [u8; LEN] {
    debug_assert!(LEN <= 256, "stack-allocated bytes must be less than 256");
    let mut name = [0u8; LEN];
    if name_ptr.is_null() {
        return name;
    }

    let c_str = unsafe { core::ffi::CStr::from_ptr(name_ptr) };
    let bytes = c_str.to_bytes();
    let len = core::cmp::min(bytes.len(), LEN - 1);
    name[..len].copy_from_slice(&bytes[..len]);

    name
}

/// Macro to create OS adapter types with name field and optional additional fields
/// This macro creates new types that wrap Arc<T> with an additional name field and custom fields
#[macro_export]
macro_rules! os_adapter {
    // Basic version with required name prefix (no additional fields)
    // Syntax: (prefix1 "name1" -> type1: inner_type1, prefix2 "name2" -> type2: inner_type2, ...)
    ($($prefix:expr => $name:ident: $inner_type:ty),* $(,)?) => {
        $(
            #[allow(non_upper_case_globals)]
            static $name: core::sync::atomic::AtomicUsize = core::sync::atomic::AtomicUsize::new(1);

            #[repr(C)]
            #[derive(Debug)]
            pub struct $name {
                pub inner: Arc<$inner_type>,
                pub name: [u8; $crate::MAX_NAME_LEN],
            }

            impl $name {
                /// Create a new adapter with the given inner object and name
                pub fn new(inner: Arc<$inner_type>, name: [u8; $crate::MAX_NAME_LEN]) -> Self {
                    Self { inner, name }
                }

                /// Create a new adapter with a default name plus counter
                pub fn with_default_name(inner: Arc<$inner_type>) -> Self {
                    let mut name = [0u8; $crate::MAX_NAME_LEN];
                    let name_str = $prefix;
                    let counter = $name.fetch_add(1, core::sync::atomic::Ordering::Relaxed);
                    let name_with_counter = alloc::format!("{}{}", name_str, counter);
                    let bytes = name_with_counter.as_bytes();
                    let len = core::cmp::min(bytes.len(), $crate::MAX_NAME_LEN - 1);
                    name[..len].copy_from_slice(&bytes[..len]);
                    Self { inner, name }
                }

                /// Create a new adapter with a custom name from C string
                pub fn with_name(inner: Arc<$inner_type>, name_ptr: *const core::ffi::c_char) -> Self {
                    if name_ptr.is_null() {
                        return Self::with_default_name(inner);
                    }
                    let name = $crate::bridge_utils::c_name_to_bytes::<{ $crate::MAX_NAME_LEN }>(name_ptr);
                    Self { inner, name }
                }

                /// Get a reference to the inner object
                pub fn inner(&self) -> &Arc<$inner_type> {
                    &self.inner
                }

                /// Get a mutable reference to the inner object
                pub fn inner_mut(&mut self) -> &mut Arc<$inner_type> {
                    &mut self.inner
                }

                /// Get the name of this adapter as a string slice
                pub fn name(&self) -> &str {
                    // Find the null terminator or use the full array
                    let null_pos = self.name.iter().position(|&b| b == 0).unwrap_or($crate::MAX_NAME_LEN);
                    core::str::from_utf8(&self.name[..null_pos]).unwrap_or("")
                }

                /// Set the name of this adapter
                pub fn set_name(&mut self, name: &str) {
                    let bytes = name.as_bytes();
                    let len = core::cmp::min(bytes.len(), $crate::MAX_NAME_LEN - 1);
                    self.name[..len].copy_from_slice(&bytes[..len]);
                    // Null terminate if the string is shorter than MAX_NAME_LEN bytes
                    if len < $crate::MAX_NAME_LEN {
                        self.name[len] = 0;
                    }
                }

                /// Get the raw name bytes
                pub fn name_bytes(&self) -> &[u8; $crate::MAX_NAME_LEN] {
                    &self.name
                }

                /// Clone the inner Arc
                pub fn clone_inner(&self) -> Arc<$inner_type> {
                    Arc::clone(&self.inner)
                }
            }
        )*
    };

    // Extended version with additional fields
    ($prefix:expr => $name:ident: $inner_type:ty { $($field:ident: $field_type:ty),* $(,)? }) => {
        #[allow(non_upper_case_globals)]
        static $name: core::sync::atomic::AtomicUsize = core::sync::atomic::AtomicUsize::new(1);

        #[repr(C)]
        #[derive(Debug)]
        pub struct $name {
            pub inner: $crate::Arc<$inner_type>,
            pub name: [u8; $crate::MAX_NAME_LEN],

            $(
                pub $field: $field_type,
            )*
        }

        impl $name {
            /// Create a new adapter with the given inner object, name, and additional fields
            pub fn new(inner: $crate::Arc<$inner_type>, name: [u8; $crate::MAX_NAME_LEN], $($field: $field_type),*) -> Self {
                Self {
                    inner,
                    name,
                    $($field,)*
                }
            }

            /// Create a new adapter with a default name plus counter and additional fields
            pub fn with_default_name(inner: $crate::Arc<$inner_type>) -> Self {
                let mut name = [0u8; $crate::MAX_NAME_LEN];
                let name_str = $prefix;
                let counter = $name.fetch_add(1, core::sync::atomic::Ordering::Relaxed);
                let name_with_counter = alloc::format!("{}{}", name_str, counter);
                let bytes = name_with_counter.as_bytes();
                let len = core::cmp::min(bytes.len(), $crate::MAX_NAME_LEN - 1);
                name[..len].copy_from_slice(&bytes[..len]);
                Self {
                    inner,
                    name,
                    $($field: <$field_type>::default(),)*
                }
            }

            /// Create a new adapter with a custom name from C string and additional fields
            pub fn with_name(inner: Arc<$inner_type>, name_ptr: *const core::ffi::c_char) -> Self {
                if name_ptr.is_null() {
                    return Self::with_default_name(inner);
                }
                let name = $crate::bridge_utils::c_name_to_bytes::<{ $crate::MAX_NAME_LEN }>(name_ptr);
                Self {
                    inner,
                    name,
                    $($field: <$field_type>::default(),)*
                }
            }

            /// Get a reference to the inner object
            pub fn inner(&self) -> &$crate::Arc<$inner_type> {
                &self.inner
            }

            /// Get a mutable reference to the inner object
            pub fn inner_mut(&mut self) -> &mut $crate::Arc<$inner_type> {
                &mut self.inner
            }

            /// Get the name of this adapter as a string slice
            pub fn name(&self) -> &str {
                // Find the null terminator or use the full array
                let null_pos = self.name.iter().position(|&b| b == 0).unwrap_or($crate::MAX_NAME_LEN);
                core::str::from_utf8(&self.name[..null_pos]).unwrap_or("")
            }

            /// Set the name of this adapter
            pub fn set_name(&mut self, name: &str) {
                let bytes = name.as_bytes();
                let len = core::cmp::min(bytes.len(), $crate::MAX_NAME_LEN - 1);
                self.name[..len].copy_from_slice(&bytes[..len]);
                // Null terminate if the string is shorter than MAX_NAME_LEN bytes
                if len < $crate::MAX_NAME_LEN {
                    self.name[len] = 0;
                }
            }

            /// Get the raw name bytes
            pub fn name_bytes(&self) -> &[u8; $crate::MAX_NAME_LEN] {
                &self.name
            }

            /// Clone the inner Arc
            pub fn clone_inner(&self) -> $crate::Arc<$inner_type> {
                $crate::Arc::clone(&self.inner)
            }
        }
    };
}
