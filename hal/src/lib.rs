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

//! Hardware Abstraction Layer (HAL) for the Kernel

#![no_std]

pub mod err;
use core::num::NonZeroUsize;

use err::Result;
pub mod clock_control;
pub mod i2c;
pub mod pinctrl;
pub mod reset;
pub mod uart;

/// Hardware abstraction layer peripheral configuration trait
///
/// Provides a unified interface for configuring peripherals with generic parameter types.
/// This trait allows different peripheral types to be configured in a type-safe manner
/// using specific configuration parameters.
///
/// # Type Parameters
///
/// * `P` - The configuration parameter type that contains the settings needed
///         to configure the peripheral
/// # Associated Types
///
/// * `Target` - The type returned after peripheral configuration. Typically this is the `()` type,
///              indicating completion of the configuration operation. In certain scenarios, such as
///              GPIO Port configurations, the peripheral may return different types like `Input` and
///              `Output` based on the parameter type, enabling compile-time state type checking.
pub trait Configuration<P> {
    type Target;
    fn configure(&self, param: &P) -> Result<Self::Target>;
}

/// Platform peripheral base trait
///
/// Defines the fundamental operations that all platform peripherals must implement.
/// This trait provides a unified interface for enabling and disabling peripheral devices
/// across different hardware platforms.
///
/// All peripheral drivers should implement this trait to ensure consistent power
/// management and resource control capabilities.
///
/// # Trait Bounds
///
/// This trait requires implementations to be:
/// - `Sync` - Safe to share references between threads, Peripherals are often accessed from multiple contexts.
/// - `Send` - Safe to transfer ownership between threads, Peripherals always exists in system memory.
/// - `'static` - Lives for the entire duration of the program
///
/// These bounds ensure that peripheral instances can be safely used in multi-threaded
/// environments and stored in static variables, which is common in embedded systems.
pub trait PlatPeri: Sync + Send + 'static {
    fn enable(&self) {}
    fn disable(&self) {}
}

/// Line status register operations trait
///
/// Provides a standard interface for reading and checking communication line status.
/// This trait is primarily used for communication peripherals such as UART, SPI, I2C, etc.
///
pub trait HasLineStatusReg {
    /// Check if the bus is busy
    ///
    /// This method reads the line status register to determine if the communication
    /// bus is currently busy with data transmission or other operations.
    ///
    /// # Returns
    ///
    /// * `true` - The bus is currently transmitting data or in a busy state
    /// * `false` - The bus is idle and ready for new transmissions
    ///
    /// # Usage
    ///
    /// This method is typically used to ensure the bus is idle before starting
    /// a new transmission, preventing data corruption or transmission conflicts.
    fn is_bus_busy(&self) -> bool;
}

/// 8-bit data register operations trait
///
/// Provides a standard interface for reading and writing 8-bit data registers.
/// This trait is suitable for peripherals that support 8-bit data transfers,
/// such as UART, SPI, I2C, and other communication interfaces.
///
pub trait Has8bitDataReg {
    fn read_data8(&self) -> Result<u8>;
    fn write_data8(&self, data: u8);

    fn is_data_ready(&self) -> bool;
}

/// Interrupt register operations trait
///
/// Provides a standard interface for interrupt configuration and management.
/// This trait allows peripherals to configure, enable, disable, and handle
/// various types of interrupts in a type-safe manner.
///
/// # Type Parameters
///
/// * `InterruptType` - The interrupt type, typically an enum or bitfield type
///                     that defines the specific interrupts supported by the peripheral
///
/// NOTE: this trait is unstable and may change in future releases.
pub trait HasInterruptReg {
    type InterruptType;
    fn enable_interrupt(&self, intr: Self::InterruptType);
    fn disable_interrupt(&self, intr: Self::InterruptType);
    fn get_interrupt(&self) -> Self::InterruptType;

    // FIXME: dyn trait object may is not efficient enough
    fn set_interrupt_handler(&self, handler: &'static dyn Fn());

    fn clear_interrupt(&self, intr: Self::InterruptType);
    fn get_irq_nums(&self) -> &[u32];
}

/// FIFO (First-In-First-Out) operations trait
///
/// Provides a standard interface for FIFO buffer management in peripherals.
/// This trait is suitable for peripherals that support hardware FIFOs,
/// such as UART, SPI, I2C, and other communication interfaces.
///
pub trait HasFifo {
    fn enable_fifo(&self, num: u8) -> Result<()>;
    fn is_tx_fifo_full(&self) -> bool;
    fn is_rx_fifo_empty(&self) -> bool;
}

/// Status register operations trait
///
/// Provides a standard interface for reading peripheral status information.
/// This trait allows peripherals to expose their current operational state
/// in a structured and type-safe manner.
///
/// # Type Parameters
///
/// * `StatusType` - The status type, typically a struct or enum that contains
///                  the peripheral's status information
///
pub trait HasErrorStatusReg {
    type ErrorStatusType;
    fn get_error_status(&self) -> Self::ErrorStatusType;
}

/// Reset register operations trait
///
/// Provides a standard interface for resetting and unresetting peripherals.
/// This trait allows peripherals to be reset to their default state or
/// brought out of reset in a type-safe manner.
///
pub trait HasRestReg {
    fn reset(&self);
    fn unreset(&self);
}
