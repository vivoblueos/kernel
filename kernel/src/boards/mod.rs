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

use blueos_macro::current_board_mod;

current_board_mod!();

#[macro_export]
macro_rules! define_peripheral {
    ($( ($field_name:ident, $device_ty:ty, $v:expr) ),* $(,)?) => {
        paste::paste! {
            $(
                pub static [<$field_name:upper>]: $device_ty = $v;
                pub static [<$field_name:upper _DEVICE_DATA>]: crate::devices::DeviceData = crate::devices::new_native_device_data(&[<$field_name:upper>]);
            )*
        }

        #[macro_export]
        macro_rules! get_device {
            $(
                ($field_name) => {
                    paste::paste! { &crate::boards::[<$field_name:upper>] }
                };
            )*
        }

        #[macro_export]
        macro_rules! get_device_data {
            $(
                ($field_name) => {
                    paste::paste! { &crate::boards::[<$field_name:upper _DEVICE_DATA>] }
                };
            )*
        }

        pub use get_device;
        pub use get_device_data;
    };
}

#[macro_export]
macro_rules! define_pin_states {
    ($class_name:ty, $( ( $($v:expr),* $(,)? ) ),* $(,)?) => {
        pub(crate) const PIN_STATES: &[&$class_name] = &[
            $( &<$class_name>::new( $($v),* ), )*
        ];
    };
    (None) => {
        pub(crate) const PIN_STATES: &[&()] = &[];
    }
}

#[macro_export]
macro_rules! define_bus {
    ($( ($bus_name:ident, $bus_ty:ty, $( ($device_name:ident, $device_ty:ty, $device:expr) ),* $(,)?  ) ),* $(,)?) => {
        $(
            paste::paste! {
                $(
                    pub static [<$device_name:upper>]: $device_ty = $device;
                    pub static [<$device_name:upper _DEVICE_DATA>]: crate::devices::DeviceData = crate::devices::new_native_device_data(&[<$device_name:upper>]);
                )*
            }

            paste::paste! {
                pub static [<$bus_name:upper _DATA>]: &[&crate::devices::DeviceData] = &[
                    $(
                        &[<$device_name:upper _DEVICE_DATA>],
                    )*
                ];
            }
        )*

        #[macro_export]
        macro_rules! get_bus_devices {
            $(
                ($bus_name) => {
                    paste::paste! { crate::boards::[<$bus_name:upper _DATA>] }
                };
            )*
        }

        #[macro_export]
        macro_rules! get_bus_ty {
            $(
                ($bus_name) => {
                    $bus_ty
                };
            )*
        }

        pub use get_bus_ty;
        pub use get_bus_devices;
    };
}
