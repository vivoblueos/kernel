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

// This code is based on [tock](https://github.com/tock/tock/blob/master/chips/rp2040/src/i2c.rs)

// Licensed under the Apache License, Version 2.0 or the MIT License.
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright Tock Contributors 2022.

use blueos_hal::{Configuration, Has8bitDataReg, HasErrorStatusReg, HasFifo, PlatPeri};
use tock_registers::{
    interfaces::{ReadWriteable, Readable, Writeable},
    register_bitfields, register_structs,
    registers::{ReadOnly, ReadWrite},
};

use crate::static_ref::StaticRef;

register_structs! {
    I2cRegisters {
        (0x00 => ic_con: ReadWrite<u32, IC_CON::Register>),
        (0x04 => ic_tar: ReadWrite<u32, IC_TAR::Register>),
        (0x08 => ic_sar: ReadWrite<u32, IC_SAR::Register>),
        (0x0c => _reserved0),
        (0x10 => ic_data_cmd: ReadWrite<u32, IC_DATA_CMD::Register>),
        (0x14 => ic_ss_scl_hcnt: ReadWrite<u32, IC_SS_SCL_HCNT::Register>),
        (0x18 => ic_ss_scl_lcnt: ReadWrite<u32, IC_SS_SCL_LCNT::Register>),
        (0x1c => ic_fs_scl_hcnt: ReadWrite<u32, IC_FS_SCL_HCNT::Register>),
        (0x20 => ic_fs_scl_lcnt: ReadWrite<u32, IC_FS_SCL_LCNT::Register>),
        (0x24 => _reserved1),
        (0x2c => ic_intr_stat: ReadOnly<u32, IC_INTR_STAT::Register>),
        (0x30 => ic_intr_mask: ReadWrite<u32, IC_INTR_MASK::Register>),
        (0x34 => ic_raw_intr_stat: ReadOnly<u32, IC_RAW_INTR_STAT::Register>),
        (0x38 => ic_rx_tl: ReadWrite<u32, IC_RX_TL::Register>),
        (0x3c => ic_tx_tl: ReadWrite<u32, IC_TX_TL::Register>),
        (0x40 => ic_clr_intr: ReadOnly<u32, IC_CLR_INTR::Register>),
        (0x44 => _reserved2), // TODO: there are still some registers to list in this gap
        (0x54 => ic_clr_tx_abrt: ReadOnly<u32, IC_CLR_TX_ABRT::Register>),
        (0x58 => _reserved3), // TODO: there are still some registers to list in this gap
        (0x60 => ic_clr_stop_det: ReadOnly<u32, IC_CLR_STOP_DET::Register>),
        (0x64 => _reserved4), // TODO: there are still some registers to list in this gap
        (0x6c => ic_enable: ReadWrite<u32, IC_ENABLE::Register>),
        (0x70 => ic_status: ReadOnly<u32, IC_STATUS::Register>),
        (0x74 => _reserved5),
        (0x7c => ic_sda_hold: ReadWrite<u32, IC_SDA_HOLD::Register>),
        (0x80 => ic_tx_abrt_source: ReadOnly<u32, IC_TX_ABRT_SOURCE::Register>),
        (0x84 => _reserved6), // TODO: there are still some registers to list in this gap
        (0x88 => ic_dma_cr: ReadWrite<u32, IC_DMA_CR::Register>),
        (0x8c => _reserved7), // TODO: there are still some registers to list in this gap
        (0xa0 => ic_fs_spklen: ReadWrite<u32, IC_FS_SPKLEN::Register>),
        (0xa4 => @END), // TODO: there are still some more registers to list here
    }
}

register_bitfields! [u32,
    /// I2C Control Register
    IC_CON [
        MASTER_MODE OFFSET(0) NUMBITS(1) [],
        SPEED OFFSET(1) NUMBITS(2) [
            STANDARD = 0x1,
            FAST = 0x2,
            HIGH = 0x3,
        ],
        IC_10BITADDR_SLAVE OFFSET(3) NUMBITS(1) [],
        IC_10BITADDR_MASTER OFFSET(4) NUMBITS(1) [],
        IC_RESTART_EN OFFSET(5) NUMBITS(1) [],
        IC_SLAVE_DISABLE OFFSET(6) NUMBITS(1) [],
        STOP_DET_IFADDRESSED OFFSET(7) NUMBITS(1) [],
        TX_EMPTY_CTRL OFFSET(8) NUMBITS(1) [],
        RX_FIFO_FULL_HLD_CTRL OFFSET(9) NUMBITS(1) [],
        STOP_DET_IF_MASTER_ACTIVE OFFSET(10) NUMBITS(1) [],
    ],
    /// I2C Target Address Register
    IC_TAR [
        IC_TAR OFFSET(0) NUMBITS(10) [],
        GC_OR_START OFFSET(10) NUMBITS(1) [],
        SPECIAL OFFSET(11) NUMBITS(1) [],
    ],
    /// I2C Slave Address Register
    IC_SAR [
        IC_SAR OFFSET(0) NUMBITS(10) [],
    ],
    /// I2C Rx/Tx Data Buffer and Command Register
    IC_DATA_CMD [
        DAT OFFSET(0) NUMBITS(8) [],
        CMD OFFSET(8) NUMBITS(1) [],
        STOP OFFSET(9) NUMBITS(1) [],
        RESTART OFFSET(10) NUMBITS(1) [],
        FIRST_DATA_BYTE OFFSET(11) NUMBITS(1) [],
    ],
    /// Standard Speed I2C Clock SCL High Count Register
    IC_SS_SCL_HCNT [
        IC_SS_SCL_HCNT OFFSET(0) NUMBITS(16) [],
    ],
    /// Standard Speed I2C Clock SCL Low Count Register
    IC_SS_SCL_LCNT [
        IC_SS_SCL_LCNT OFFSET(0) NUMBITS(16) [],
    ],
    /// Fast Mode or Fast Mode Plus I2C Clock SCL High Count Register
    IC_FS_SCL_HCNT [
        IC_FS_SCL_HCNT OFFSET(0) NUMBITS(16) [],
    ],
    /// Fast Mode or Fast Mode Plus I2C Clock SCL Low Count Register
    IC_FS_SCL_LCNT [
        IC_FS_SCL_LCNT OFFSET(0) NUMBITS(16) [],
    ],
    /// I2C Interrupt Status Register
    IC_INTR_STAT [
        R_RX_UNDER OFFSET(0) NUMBITS(1) [],
        R_RX_OVER OFFSET(1) NUMBITS(1) [],
        R_RX_FULL OFFSET(2) NUMBITS(1) [],
        R_TX_OVER OFFSET(3) NUMBITS(1) [],
        R_TX_EMPTY OFFSET(4) NUMBITS(1) [],
        R_RD_REQ OFFSET(5) NUMBITS(1) [],
        R_TX_ABRT OFFSET(6) NUMBITS(1) [],
        R_RX_DONE OFFSET(7) NUMBITS(1) [],
        R_ACTIVITY OFFSET(8) NUMBITS(1) [],
        R_STOP_DET OFFSET(9) NUMBITS(1) [],
        R_START_DET OFFSET(10) NUMBITS(1) [],
        R_GEN_CALL OFFSET(11) NUMBITS(1) [],
        R_RESTART_DET OFFSET(12) NUMBITS(1) [],
    ],
    /// I2C Interrupt Mask Register
    IC_INTR_MASK [
        M_RX_UNDER OFFSET(0) NUMBITS(1) [],
        M_RX_OVER OFFSET(1) NUMBITS(1) [],
        M_RX_FULL OFFSET(2) NUMBITS(1) [],
        M_TX_OVER OFFSET(3) NUMBITS(1) [],
        M_TX_EMPTY OFFSET(4) NUMBITS(1) [],
        M_RD_REQ OFFSET(5) NUMBITS(1) [],
        M_TX_ABRT OFFSET(6) NUMBITS(1) [],
        M_RX_DONE OFFSET(7) NUMBITS(1) [],
        M_ACTIVITY OFFSET(8) NUMBITS(1) [],
        M_STOP_DET OFFSET(9) NUMBITS(1) [],
        M_START_DET OFFSET(10) NUMBITS(1) [],
        M_GEN_CALL OFFSET(11) NUMBITS(1) [],
        M_RESTART_DET OFFSET(12) NUMBITS(1) [],
    ],
    /// I2C Raw Interrupt Status Register
    IC_RAW_INTR_STAT [
        RX_UNDER OFFSET(0) NUMBITS(1) [],
        RX_OVER OFFSET(1) NUMBITS(1) [],
        RX_FULL OFFSET(2) NUMBITS(1) [],
        TX_OVER OFFSET(3) NUMBITS(1) [],
        TX_EMPTY OFFSET(4) NUMBITS(1) [],
        RD_REQ OFFSET(5) NUMBITS(1) [],
        TX_ABRT OFFSET(6) NUMBITS(1) [],
        RX_DONE OFFSET(7) NUMBITS(1) [],
        ACTIVITY OFFSET(8) NUMBITS(1) [],
        STOP_DET OFFSET(9) NUMBITS(1) [],
        START_DET OFFSET(10) NUMBITS(1) [],
        GEN_CALL OFFSET(11) NUMBITS(1) [],
        RESTART_DET OFFSET(12) NUMBITS(1) [],
    ],
    /// I2C Receive FIFO Threshold Register
    IC_RX_TL [
        IC_RX_TL OFFSET(0) NUMBITS(8) [],
    ],
    /// I2C Transmit FIFO Threshold Register
    IC_TX_TL [
        IC_TX_TL OFFSET(0) NUMBITS(8) [],
    ],
    /// Clear Combined and Individual Interrupt Register
    IC_CLR_INTR [
        CLR_INTR OFFSET(0) NUMBITS(1) [],
    ],
    /// Clear TX_ABRT Interrupt Register
    IC_CLR_TX_ABRT [
        CLR_TX_ABRT OFFSET(0) NUMBITS(1) [],
    ],
    /// Clear STOP_DET Interrupt Register
    IC_CLR_STOP_DET [
        CLR_STOP_DET OFFSET(0) NUMBITS(1) [],
    ],
    /// I2C Enable Register
    IC_ENABLE [
        ENABLE OFFSET(0) NUMBITS(1) [],
        ABORT OFFSET(1) NUMBITS(1) [],
        TX_CMD_BLOCK OFFSET(2) NUMBITS(1) [],
    ],
    /// I2C Status Register
    IC_STATUS [
        SLV_ACTIVITY OFFSET(6) NUMBITS(1) [],
        MST_ACTIVITY OFFSET(5) NUMBITS(1) [],
        RFF OFFSET(4) NUMBITS(1) [],
        RFNE OFFSET(3) NUMBITS(1) [],
        TFE OFFSET(2) NUMBITS(1) [],
        TFNF OFFSET(1) NUMBITS(1) [],
        ACTIVITY OFFSET(0) NUMBITS(1) [],
    ],
    /// I2C SDA Hold Time Length Register
    IC_SDA_HOLD [
        IC_SDA_TX_HOLD OFFSET(0) NUMBITS(16) [],
        IC_SDA_RX_HOLD OFFSET(16) NUMBITS(8) [],
    ],
    /// I2C Transmit Abort Source Register
    IC_TX_ABRT_SOURCE [
        ABRT_7B_ADDR_NOACK OFFSET(0) NUMBITS(1) [],
        ABRT_10ADDR1_NOACK OFFSET(1) NUMBITS(1) [],
        ABRT_10ADDR2_NOACK OFFSET(2) NUMBITS(1) [],
        ABRT_TXDATA_NOACK OFFSET(3) NUMBITS(1) [],
        ABRT_GCALL_NOACK OFFSET(4) NUMBITS(1) [],
        ABRT_GCALL_READ OFFSET(5) NUMBITS(1) [],
        ABRT_HS_ACKDET OFFSET(6) NUMBITS(1) [],
        ABRT_SBYTE_ACKDET OFFSET(7) NUMBITS(1) [],
        ABRT_HS_NORSTRT OFFSET(8) NUMBITS(1) [],
        ABRT_SBYTE_NORSTRT OFFSET(9) NUMBITS(1) [],
        ABRT_10B_RD_NORSTRT OFFSET(10) NUMBITS(1) [],
        ABRT_MASTER_DIS OFFSET(11) NUMBITS(1) [],
        ARB_LOST OFFSET(12) NUMBITS(1) [],
        ABRT_SLVFLUSH_TXFIFO OFFSET(13) NUMBITS(1) [],
        ABRT_SLV_ARBLOST OFFSET(14) NUMBITS(1) [],
        ABRT_SLVRD_INTX OFFSET(15) NUMBITS(1) [],
        ABRT_USER_ABRT OFFSET(16) NUMBITS(1) [],
        TX_FLUSH_CNT OFFSET(23) NUMBITS(9) [],
    ],
    /// DMA Control Register
    IC_DMA_CR [
        RDMAE OFFSET(0) NUMBITS(1) [],
        TDMAE OFFSET(1) NUMBITS(1) [],
    ],
    /// I2C SS, FS or FM+ spike suppression limit
    IC_FS_SPKLEN [
        IC_FS_SPKLEN OFFSET(0) NUMBITS(8) [],
    ],
];

pub struct I2cDw {
    registers: StaticRef<I2cRegisters>,
    clk: u32,
    pub reset_ctrl: Option<(&'static dyn blueos_hal::reset::ResetCtrlWithDone, u32)>,
}

impl I2cDw {
    pub const fn new(
        base: usize,
        clk: u32,
        reset_ctrl: Option<(&'static dyn blueos_hal::reset::ResetCtrlWithDone, u32)>,
    ) -> Self {
        I2cDw {
            registers: unsafe { StaticRef::new(base as *const I2cRegisters) },
            clk,
            reset_ctrl,
        }
    }

    fn set_baudrate(&self, baudrate: u32) -> u32 {
        assert!(baudrate != 0);

        let freq_in = self.clk;

        let period = (freq_in + baudrate / 2) / baudrate;
        let lcnt = period * 3 / 5;
        let hcnt = period - lcnt;
        assert!(hcnt >= 8);
        assert!(lcnt >= 8);

        let sda_tx_hold_count = if baudrate < 1000000 {
            ((freq_in * 3) / 10000000) + 1
        } else {
            ((freq_in * 3) / 25000000) + 1
        };
        assert!(sda_tx_hold_count <= lcnt - 2);

        // Always use "fast" mode (<= 400 kHz, works fine for standard mode too)
        self.registers.ic_con.modify(IC_CON::SPEED::FAST);
        self.registers.ic_fs_scl_hcnt.set(hcnt);
        self.registers.ic_fs_scl_lcnt.set(lcnt);
        self.registers.ic_fs_spklen.set({
            if lcnt < 16 {
                1
            } else {
                lcnt / 16
            }
        });
        self.registers
            .ic_sda_hold
            .modify(IC_SDA_HOLD::IC_SDA_TX_HOLD.val(sda_tx_hold_count));

        freq_in / period
    }

    #[inline]
    fn read_and_clr_err(&self) -> blueos_hal::err::Result<u32> {
        let err = self.registers.ic_tx_abrt_source.get();
        if err != 0 {
            self.registers.ic_clr_tx_abrt.get();
            Err(blueos_hal::err::HalError::Fail)
        } else {
            Ok(err)
        }
    }
}

unsafe impl Send for I2cDw {}
unsafe impl Sync for I2cDw {}

impl PlatPeri for I2cDw {
    fn enable(&self) {
        self.registers.ic_enable.set(1);
    }

    fn disable(&self) {
        self.registers.ic_enable.set(0);
    }
}

impl Configuration<super::I2cConfig> for I2cDw {
    type Target = ();
    fn configure(&self, param: &super::I2cConfig) -> blueos_hal::err::Result<Self::Target> {
        if let Some(ref reset_ctrl) = self.reset_ctrl {
            let (reset_ctrl, reset_id) = reset_ctrl;
            reset_ctrl.set_reset(*reset_id);
            reset_ctrl.clear_reset(*reset_id);
            reset_ctrl.wait_done(*reset_id);
        }

        self.disable();

        // Configure as a fast-mode master with RepStart support, 7-bit addresses
        self.registers.ic_con.write(
            IC_CON::SPEED::FAST
                + IC_CON::MASTER_MODE::SET
                + IC_CON::IC_SLAVE_DISABLE::SET
                + IC_CON::IC_RESTART_EN::SET
                + IC_CON::TX_EMPTY_CTRL::SET,
        );

        // Set the TX and RX thresholds to 1 (encoded by the value 0) so that we
        // get an interrupt whenever a byte is available to be read or written.
        //
        // TODO: this is obviously not optimal for efficiency
        self.enable_fifo(1)?;

        self.set_baudrate(param.baudrate);
        self.enable();

        Ok(())
    }
}

impl HasFifo for I2cDw {
    fn enable_fifo(&self, num: u8) -> blueos_hal::err::Result<()> {
        let num = num as u32;
        self.registers.ic_tx_tl.set(num);
        self.registers.ic_rx_tl.set(num);
        Ok(())
    }

    fn is_tx_fifo_full(&self) -> bool {
        self.registers.ic_status.is_set(IC_STATUS::TFNF) == false
    }

    fn is_rx_fifo_empty(&self) -> bool {
        self.registers.ic_status.is_set(IC_STATUS::RFNE) == false
    }
}

impl blueos_hal::Has8bitDataReg for I2cDw {
    fn write_data8(&self, data: u8) {
        self.registers
            .ic_data_cmd
            .write(IC_DATA_CMD::DAT.val(data as u32) + IC_DATA_CMD::CMD::CLEAR);
    }

    fn read_data8(&self) -> blueos_hal::err::Result<u8> {
        self.registers.ic_data_cmd.write(IC_DATA_CMD::CMD::SET);
        while self.is_data_ready() == false {
            self.read_and_clr_err()?;
        }
        Ok(self.registers.ic_data_cmd.read(IC_DATA_CMD::DAT) as u8)
    }

    fn is_data_ready(&self) -> bool {
        self.registers.ic_status.is_set(IC_STATUS::RFNE)
    }
}

impl blueos_hal::i2c::I2c<super::I2cConfig, ()> for I2cDw {
    fn set_address(&self, address: u16) -> blueos_hal::err::Result<()> {
        self.registers.ic_enable.set(0);
        self.registers
            .ic_tar
            .modify(IC_TAR::IC_TAR.val(address as u32));
        self.registers.ic_enable.set(1);
        Ok(())
    }

    fn read_byte_with_stop(&self) -> blueos_hal::err::Result<u8> {
        self.registers
            .ic_data_cmd
            .write(IC_DATA_CMD::STOP::SET + IC_DATA_CMD::CMD::SET);
        while self.is_data_ready() == false {
            self.read_and_clr_err()?;
        }
        Ok(self.registers.ic_data_cmd.read(IC_DATA_CMD::DAT) as u8)
    }

    fn send_byte_with_stop(&self, byte: u8) -> blueos_hal::err::Result<()> {
        self.registers.ic_data_cmd.write(
            IC_DATA_CMD::DAT.val(byte as u32) + IC_DATA_CMD::STOP::SET + IC_DATA_CMD::CMD::CLEAR,
        );
        Ok(())
    }

    fn release_bus(&self) -> blueos_hal::err::Result<()> {
        self.registers.ic_enable.modify(IC_ENABLE::ABORT::SET);
        while self.registers.ic_enable.is_set(IC_ENABLE::ABORT) {}
        while self
            .registers
            .ic_raw_intr_stat
            .is_set(IC_RAW_INTR_STAT::TX_ABRT)
            == false
        {}
        self.registers.ic_clr_tx_abrt.get();
        self.registers.ic_tx_abrt_source.get();
        Ok(())
    }
}

impl HasErrorStatusReg for I2cDw {
    type ErrorStatusType = u32;

    fn get_error_status(&self) -> Self::ErrorStatusType {
        self.registers.ic_tx_abrt_source.get()
    }

    fn clear_error_status(&self) {
        self.registers.ic_clr_tx_abrt.get();
    }
}
