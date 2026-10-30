//! MIPI DCS commands.

use crate::interface::Interface;

#[macro_use]
pub(crate) mod macros;

mod set_address_mode;
pub use set_address_mode::*;
mod set_pixel_format;
pub use set_pixel_format::*;
mod set_column_address;
pub use set_column_address::*;
mod set_page_address;
pub use set_page_address::*;
mod set_scroll_area;
pub use set_scroll_area::*;
mod set_scroll_start;
pub use set_scroll_start::*;
mod set_tearing_effect;
pub use set_tearing_effect::*;
mod set_invert_mode;
pub use set_invert_mode::*;

/// Common trait for DCS commands.
///
/// The methods in this traits are used to convert a DCS command into bytes.
pub trait DcsCommand {
    /// Returns the instruction code.
    fn instruction(&self) -> u8;

    /// Fills the given buffer with the command parameters.
    fn fill_params_buf(&self, buffer: &mut [u8]) -> usize;
}

/// An extension trait for [`Interface`] with support for writing DCS commands.
///
/// Commands which are part of the manufacturer independent user command set can be sent to the
/// display by using the [`write_command`](Self::write_command) method with one of the command types
/// in this module.
///
/// All other commands, which do not have an associated type in this module, can be sent using
/// the [`write_raw`](Self::write_raw) method.
pub trait InterfaceExt: Interface {
    /// Sends a DCS command to the display interface.
    fn write_command(&mut self, command: impl DcsCommand) -> Result<(), Self::Error> {
        let mut param_bytes: [u8; 16] = [0; 16];
        let n = command.fill_params_buf(&mut param_bytes);
        self.write_raw(command.instruction(), &param_bytes[..n])
    }

    /// Sends a raw command with the given `instruction` to the display interface.
    ///
    /// The `param_bytes` slice can contain the instruction parameters, which are sent as data after
    /// the instruction code was sent. If no parameters are required an empty slice can be passed to
    /// this method.
    ///
    /// This method is intended to be used for sending commands which are not part of the MIPI DCS
    /// user command set. Use [`write_command`](Self::write_command) for commands in the user
    /// command set.
    fn write_raw(&mut self, instruction: u8, param_bytes: &[u8]) -> Result<(), Self::Error> {
        self.send_command(instruction, param_bytes)
    }
}

impl<T: Interface> InterfaceExt for T {}

// DCS commands that don't use any parameters

dcs_basic_command!(
    /// Software Reset
    SoftReset,
    0x01
);
dcs_basic_command!(
    /// Enter Sleep Mode
    EnterSleepMode,
    0x10
);
dcs_basic_command!(
    /// Exit Sleep Mode
    ExitSleepMode,
    0x11
);
dcs_basic_command!(
    /// Enter Partial Mode
    EnterPartialMode,
    0x12
);
dcs_basic_command!(
    /// Enter Normal Mode
    EnterNormalMode,
    0x13
);
dcs_basic_command!(
    /// Turn Display Off
    SetDisplayOff,
    0x28
);

dcs_basic_command!(
    /// Turn Display On
    SetDisplayOn,
    0x29
);
dcs_basic_command!(
    /// Exit Idle Mode
    ExitIdleMode,
    0x38
);
dcs_basic_command!(
    /// Enter Idle Mode
    EnterIdleMode,
    0x39
);
// dcs_basic_command!(
//     /// Turn off Color Invert Mode
//     ExitInvertMode,
//     0x21
// );
// dcs_basic_command!(
//     /// Turn on Color Invert Mode
//     EnterInvertMode,
//     0x20
// );
dcs_basic_command!(
    /// Initiate Framebuffer Memory Write
    WriteMemoryStart,
    0x2C
);
