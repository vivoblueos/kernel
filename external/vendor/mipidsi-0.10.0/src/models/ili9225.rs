use crate::dcs::DcsCommand;
use crate::dcs::InterfaceExt;
use crate::dcs::SetAddressMode;
use crate::options;
use crate::options::{ColorOrder, Rotation};
use crate::{
    interface::Interface,
    models::{Model, ModelInitError},
    options::ModelOptions,
};
use embedded_graphics_core::pixelcolor::Rgb565;
use embedded_hal::delay::DelayNs;

/// ILI9225 display in Rgb565 color mode.
pub struct ILI9225Rgb565;

const ILI9225_POWER_CTRL1: u8 = 0x10;
const ILI9225_POWER_CTRL2: u8 = 0x11;
const ILI9225_POWER_CTRL3: u8 = 0x12;
const ILI9225_POWER_CTRL4: u8 = 0x13;
const ILI9225_POWER_CTRL5: u8 = 0x14;

const ILI9225_DRIVER_OUTPUT_CTRL: u8 = 0x01; // Driver Output Control
const ILI9225_LCD_AC_DRIVING_CTRL: u8 = 0x02; // LCD AC Driving Control
const ILI9225_ENTRY_MODE: u8 = 0x03; // Entry Mode
const ILI9225_DISP_CTRL1: u8 = 0x07; // Display Control 1
const ILI9225_BLANK_PERIOD_CTRL1: u8 = 0x08; // Blank Period Control
const ILI9225_FRAME_CYCLE_CTRL: u8 = 0x0B; // Frame Cycle Control
const ILI9225_INTERFACE_CTRL: u8 = 0x0C; // Interface Control
const ILI9225_OSC_CTRL: u8 = 0x0F; // Osc Control
const ILI9225_VCI_RECYCLING: u8 = 0x15; // Osc Control
const ILI9225_RAM_ADDR_SET1: u8 = 0x20; // Osc Control
const ILI9225_RAM_ADDR_SET2: u8 = 0x21; // Osc Control

const ILI9225_GATE_SCAN_CTRL: u8 = 0x30; // Gate Scan Control Register
const ILI9225_VERTICAL_SCROLL_CTRL1: u8 = 0x31; // Vertical Scroll Control 1 Register
const ILI9225_VERTICAL_SCROLL_CTRL2: u8 = 0x32; // Vertical Scroll Control 2 Register
const ILI9225_VERTICAL_SCROLL_CTRL3: u8 = 0x33; // Vertical Scroll Control 3 Register
const ILI9225_PARTIAL_DRIVING_POS1: u8 = 0x34; // Partial Driving Position 1 Register
const ILI9225_PARTIAL_DRIVING_POS2: u8 = 0x35; // Partial Driving Position 2 Register
const ILI9225_HORIZONTAL_WINDOW_ADDR1: u8 = 0x36; // Horizontal Address Start Position
const ILI9225_HORIZONTAL_WINDOW_ADDR2: u8 = 0x37; // Horizontal Address End Position
const ILI9225_VERTICAL_WINDOW_ADDR1: u8 = 0x38; // Vertical Address Start Position
const ILI9225_VERTICAL_WINDOW_ADDR2: u8 = 0x39; // Vertical Address End Position

const ILI9225_GAMMA_CTRL1: u8 = 0x50; // Gamma Control 1
const ILI9225_GAMMA_CTRL2: u8 = 0x51; // Gamma Control 2
const ILI9225_GAMMA_CTRL3: u8 = 0x52; // Gamma Control 3
const ILI9225_GAMMA_CTRL4: u8 = 0x53; // Gamma Control 4
const ILI9225_GAMMA_CTRL5: u8 = 0x54; // Gamma Control 5
const ILI9225_GAMMA_CTRL6: u8 = 0x55; // Gamma Control 6
const ILI9225_GAMMA_CTRL7: u8 = 0x56; // Gamma Control 7
const ILI9225_GAMMA_CTRL8: u8 = 0x57; // Gamma Control 8
const ILI9225_GAMMA_CTRL9: u8 = 0x58; // Gamma Control 9
const ILI9225_GAMMA_CTRL10: u8 = 0x59; // Gamma Control 10

fn options_write_cmd<DI>(di: &mut DI, options: &ModelOptions) -> Result<(), DI::Error>
where
    DI: Interface,
{
    // Command 1: DRIVER_OUTPUT_CTRL (0x01)
    let driver_high_byte = match options.orientation.rotation {
        Rotation::Deg0 => 0x01,
        Rotation::Deg90 => 0x00,
        Rotation::Deg180 => 0x02,
        Rotation::Deg270 => 0x03,
    };

    let driver_params = [driver_high_byte, 0x1C];
    di.write_raw(ILI9225_DRIVER_OUTPUT_CTRL, &driver_params)?;

    // Command 2: ENTRY_MODE (0x03)
    let color_order_byte = match options.color_order {
        ColorOrder::Rgb => 0x00,
        ColorOrder::Bgr => 0x10,
    };

    let entry_low_byte = if options.orientation.rotation.is_vertical() {
        0x38
    } else {
        0x30
    };
    let entry_params = [color_order_byte, entry_low_byte];
    di.write_raw(ILI9225_ENTRY_MODE, &entry_params)?;

    Ok(())
}

fn options2ctrl_low(options: &ModelOptions) -> u8 {
    0b10011
        | match options.invert_colors {
            options::ColorInversion::Normal => 0,
            options::ColorInversion::Inverted => 0b100,
        }
}

impl Model for ILI9225Rgb565 {
    type ColorFormat = Rgb565;
    const FRAMEBUFFER_SIZE: (u16, u16) = (176, 220);
    const RESET_DURATION: u32 = 1000;

    fn init<DELAY, DI>(
        &mut self,
        di: &mut DI,
        delay: &mut DELAY,
        options: &ModelOptions,
    ) -> Result<SetAddressMode, ModelInitError<DI::Error>>
    where
        DELAY: DelayNs,
        DI: Interface,
    {
        let madctl = SetAddressMode::from(options);

        /* Set SS bit and direction output from S528 to S1 */
        di.write_raw(ILI9225_POWER_CTRL1, &[0x00, 0x00])?; // Set SAP,DSTB,STB
        di.write_raw(ILI9225_POWER_CTRL2, &[0x00, 0x00])?; // Set APON,PON,AON,VCI1EN,VC
        di.write_raw(ILI9225_POWER_CTRL3, &[0x00, 0x00])?; // Set BT,DC1,DC2,DC3
        di.write_raw(ILI9225_POWER_CTRL4, &[0x00, 0x00])?; // Set GVDD
        di.write_raw(ILI9225_POWER_CTRL5, &[0x00, 0x00])?; // Set VCOMH/VCOML voltage

        delay.delay_us(40_000);

        di.write_raw(ILI9225_POWER_CTRL1, &[0x00, 0x18])?; // Set APON,PON,AON,VCI1EN,VC
        di.write_raw(ILI9225_POWER_CTRL2, &[0x61, 0x21])?; // Set BT,DC1,DC2,DC3
        di.write_raw(ILI9225_POWER_CTRL3, &[0x00, 0x6F])?; // Set GVDD   /*007F 0088 */
        di.write_raw(ILI9225_POWER_CTRL4, &[0x49, 0x5F])?; // Set VCOMH/VCOML voltage
        di.write_raw(ILI9225_POWER_CTRL5, &[0x08, 0x00])?; // Set SAP,DSTB,STB
        delay.delay_us(10_000);
        di.write_raw(ILI9225_POWER_CTRL2, &[0x10, 0x3B])?; // Set APON,PON,AON,VCI1EN,VC
        delay.delay_us(30_000);

        di.write_raw(ILI9225_LCD_AC_DRIVING_CTRL, &[0x01, 0x00])?; // set 1 line inversion

        options_write_cmd(di, options)?;
        di.write_raw(ILI9225_DISP_CTRL1, &[0x00, 0x00])?; // Display off
        di.write_raw(ILI9225_BLANK_PERIOD_CTRL1, &[0x08, 0x08])?; // set the back porch and front porch
        di.write_raw(ILI9225_FRAME_CYCLE_CTRL, &[0x11, 0x00])?; // set the clocks number per line
        di.write_raw(ILI9225_INTERFACE_CTRL, &[0x00, 0x00])?; // CPU  interface
        di.write_raw(ILI9225_OSC_CTRL, &[0x0F, 0x01])?; // Set Osc  /*0e01*/
        di.write_raw(ILI9225_VCI_RECYCLING, &[0x00, 0x20])?; // Set VCI recycling
        di.write_raw(ILI9225_RAM_ADDR_SET1, &[0x00, 0x00])?; // RAM Address
        di.write_raw(ILI9225_RAM_ADDR_SET2, &[0x00, 0x00])?; // RAM Address

        /* Set GRAM area */
        di.write_raw(ILI9225_GATE_SCAN_CTRL, &[0x00, 0x00])?;
        di.write_raw(ILI9225_VERTICAL_SCROLL_CTRL1, &[0x00, 0xDB])?;
        di.write_raw(ILI9225_VERTICAL_SCROLL_CTRL2, &[0x00, 0x00])?;
        di.write_raw(ILI9225_VERTICAL_SCROLL_CTRL3, &[0x00, 0x00])?;
        di.write_raw(ILI9225_PARTIAL_DRIVING_POS1, &[0x00, 0xDB])?;
        di.write_raw(ILI9225_PARTIAL_DRIVING_POS2, &[0x00, 0x00])?;
        di.write_raw(ILI9225_HORIZONTAL_WINDOW_ADDR1, &[0x00, 0xAF])?;
        di.write_raw(ILI9225_HORIZONTAL_WINDOW_ADDR2, &[0x00, 0x00])?;
        di.write_raw(ILI9225_VERTICAL_WINDOW_ADDR1, &[0x00, 0xDB])?;
        di.write_raw(ILI9225_VERTICAL_WINDOW_ADDR2, &[0x00, 0x00])?;

        /* Set GAMMA curve */
        di.write_raw(ILI9225_GAMMA_CTRL1, &[0x00, 0x00])?;
        di.write_raw(ILI9225_GAMMA_CTRL2, &[0x08, 0x08])?;
        di.write_raw(ILI9225_GAMMA_CTRL3, &[0x08, 0x0A])?;
        di.write_raw(ILI9225_GAMMA_CTRL4, &[0x00, 0x0A])?;
        di.write_raw(ILI9225_GAMMA_CTRL5, &[0x0A, 0x08])?;
        di.write_raw(ILI9225_GAMMA_CTRL6, &[0x08, 0x08])?;
        di.write_raw(ILI9225_GAMMA_CTRL7, &[0x00, 0x00])?;
        di.write_raw(ILI9225_GAMMA_CTRL8, &[0x0A, 0x00])?;
        di.write_raw(ILI9225_GAMMA_CTRL9, &[0x07, 0x10])?;
        di.write_raw(ILI9225_GAMMA_CTRL10, &[0x07, 0x10])?;

        di.write_raw(ILI9225_DISP_CTRL1, &[0x00, 0x12])?;
        delay.delay_us(50_000);

        let low = options2ctrl_low(options);

        di.write_raw(ILI9225_DISP_CTRL1, &[0x10, low])?;
        delay.delay_us(50_000);

        Ok(madctl)
    }

    fn update_address_window<DI>(
        di: &mut DI,
        rotation: Rotation,
        sx: u16,
        sy: u16,
        ex: u16,
        ey: u16,
    ) -> Result<(), DI::Error>
    where
        DI: Interface,
    {
        match rotation {
            Rotation::Deg0 | Rotation::Deg180 => {
                di.write_raw(0x37, &sx.to_be_bytes())?;
                di.write_raw(0x36, &ex.to_be_bytes())?;
                di.write_raw(0x39, &sy.to_be_bytes())?;
                di.write_raw(0x38, &ey.to_be_bytes())?;
                di.write_raw(0x20, &sx.to_be_bytes())?;
                di.write_raw(0x21, &sy.to_be_bytes())
            }
            Rotation::Deg90 | Rotation::Deg270 => {
                di.write_raw(0x39, &sx.to_be_bytes())?;
                di.write_raw(0x38, &ex.to_be_bytes())?;
                di.write_raw(0x37, &sy.to_be_bytes())?;
                di.write_raw(0x36, &ey.to_be_bytes())?;
                di.write_raw(0x21, &sx.to_be_bytes())?;
                di.write_raw(0x20, &sy.to_be_bytes())
            }
        }
    }

    fn sleep<DI, DELAY>(di: &mut DI, delay: &mut DELAY) -> Result<(), DI::Error>
    where
        DI: Interface,
        DELAY: DelayNs,
    {
        di.write_raw(ILI9225_DISP_CTRL1, &[0x00, 0x00])?;
        delay.delay_us(50_000);
        di.write_raw(ILI9225_POWER_CTRL2, &[0x00, 0x07])?;
        delay.delay_us(50_000);
        di.write_raw(ILI9225_POWER_CTRL1, &[0x0A, 0x01])
    }

    fn wake<DI, DELAY>(di: &mut DI, delay: &mut DELAY) -> Result<(), DI::Error>
    where
        DI: Interface,
        DELAY: DelayNs,
    {
        di.write_raw(ILI9225_POWER_CTRL1, &[0x0A, 0x00])?;
        di.write_raw(ILI9225_POWER_CTRL2, &[0x10, 0x3B])?;
        delay.delay_us(50_000);
        di.write_raw(ILI9225_DISP_CTRL1, &[0x10, 0x17])
    }

    fn write_memory_start<DI>(di: &mut DI) -> Result<(), DI::Error>
    where
        DI: Interface,
    {
        di.write_command(WriteMemoryStartILI9225)
    }

    fn update_options<DI>(&self, di: &mut DI, options: &ModelOptions) -> Result<(), DI::Error>
    where
        DI: Interface,
    {
        options_write_cmd(di, options)
    }
    fn set_tearing_effect<DI>(
        di: &mut DI,
        tearing_effect: options::TearingEffect,
        options: &ModelOptions,
    ) -> Result<(), DI::Error>
    where
        DI: Interface,
    {
        let low = options2ctrl_low(options);
        // Acroding the datasheet, TEMON only one bit,
        let high = match tearing_effect {
            options::TearingEffect::Off => 0,
            options::TearingEffect::Vertical => 0x10,
            options::TearingEffect::HorizontalAndVertical => 0x10,
        };

        di.write_raw(ILI9225_DISP_CTRL1, &[high, low])
    }
    fn set_vertical_scroll_region<DI>(
        _di: &mut DI,
        _top_fixed_area: u16,
        _bottom_fixed_area: u16,
    ) -> Result<(), DI::Error>
    where
        DI: Interface,
    {
        // Not support, ignore it
        Ok(())
    }
    fn set_vertical_scroll_offset<DI>(_di: &mut DI, _offset: u16) -> Result<(), DI::Error>
    where
        DI: Interface,
    {
        // Not support, ignore it
        Ok(())
    }
}

#[path = "../dcs/macros.rs"]
#[macro_use]
mod dcs_macros;

dcs_basic_command!(
    /// Initiate Framebuffer Memory Write
    WriteMemoryStartILI9225,
    0x22
);

dcs_basic_command!(
    /// Software Reset
    SoftResetILI9225,
    0x28
);
