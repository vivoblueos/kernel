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

//! ESP32-C3 I2C0 register definitions.

use core::cell::UnsafeCell;

use blueos_hal::{Configuration, Has8bitDataReg, HasErrorStatusReg, HasFifo, PlatPeri};
use tock_registers::{
    interfaces::{ReadWriteable, Readable, Writeable},
    register_bitfields, register_structs,
    registers::{ReadOnly, ReadWrite, WriteOnly},
};

use crate::static_ref::StaticRef;

const I2C_FIFO_SIZE: u32 = 32;
const ALL_INTERRUPTS: u32 = (1 << 18) - 1;
const ERROR_INTERRUPTS: u32 = (1 << 2)
    | (1 << 5)
    | (1 << 6)
    | (1 << 8)
    | (1 << 10)
    | (1 << 11)
    | (1 << 12)
    | (1 << 13)
    | (1 << 14);
const SOFTWARE_TIMEOUT: u32 = 1 << 31;
const POLL_LIMIT: u32 = 10_000_000;

register_structs! {
    pub I2cRegisters {
        (0x000 => scl_low_period: ReadWrite<u32, SCL_LOW_PERIOD::Register>),
        (0x004 => ctr: ReadWrite<u32, CTR::Register>),
        (0x008 => sr: ReadOnly<u32, SR::Register>),
        (0x00C => to: ReadWrite<u32, TO::Register>),
        (0x010 => slave_addr: ReadWrite<u32, SLAVE_ADDR::Register>),
        (0x014 => fifo_st: ReadOnly<u32, FIFO_ST::Register>),
        (0x018 => fifo_conf: ReadWrite<u32, FIFO_CONF::Register>),
        (0x01C => data: ReadWrite<u32, DATA::Register>),
        (0x020 => int_raw: ReadOnly<u32, INTERRUPT::Register>),
        (0x024 => int_clr: WriteOnly<u32, INTERRUPT::Register>),
        (0x028 => int_ena: ReadWrite<u32, INTERRUPT::Register>),
        (0x02C => int_st: ReadOnly<u32, INTERRUPT::Register>),
        (0x030 => sda_hold: ReadWrite<u32, SDA_HOLD::Register>),
        (0x034 => sda_sample: ReadWrite<u32, SDA_SAMPLE::Register>),
        (0x038 => scl_high_period: ReadWrite<u32, SCL_HIGH_PERIOD::Register>),
        (0x03C => _reserved0),
        (0x040 => scl_start_hold: ReadWrite<u32, SCL_START_HOLD::Register>),
        (0x044 => scl_rstart_setup: ReadWrite<u32, SCL_RSTART_SETUP::Register>),
        (0x048 => scl_stop_hold: ReadWrite<u32, SCL_STOP_HOLD::Register>),
        (0x04C => scl_stop_setup: ReadWrite<u32, SCL_STOP_SETUP::Register>),
        (0x050 => filter_cfg: ReadWrite<u32, FILTER_CFG::Register>),
        (0x054 => clk_conf: ReadWrite<u32, CLK_CONF::Register>),
        (0x058 => comd: [ReadWrite<u32, COMD::Register>; 8]),
        (0x078 => scl_st_time_out: ReadWrite<u32, SCL_ST_TIME_OUT::Register>),
        (0x07C => scl_main_st_time_out: ReadWrite<u32, SCL_MAIN_ST_TIME_OUT::Register>),
        (0x080 => scl_sp_conf: ReadWrite<u32, SCL_SP_CONF::Register>),
        (0x084 => scl_stretch_conf: ReadWrite<u32, SCL_STRETCH_CONF::Register>),
        (0x088 => _reserved1),
        (0x0F8 => date: ReadWrite<u32>),
        (0x0FC => _reserved2),
        (0x100 => txfifo_start_addr: ReadOnly<u32>),
        (0x104 => _reserved3),
        (0x180 => rxfifo_start_addr: ReadOnly<u32>),
        (0x184 => @END),
    }
}

register_bitfields! [
    u32,

    pub SCL_LOW_PERIOD [
        SCL_LOW_PERIOD OFFSET(0) NUMBITS(9) [],
    ],

    pub CTR [
        SDA_FORCE_OUT OFFSET(0) NUMBITS(1) [],
        SCL_FORCE_OUT OFFSET(1) NUMBITS(1) [],
        SAMPLE_SCL_LEVEL OFFSET(2) NUMBITS(1) [],
        RX_FULL_ACK_LEVEL OFFSET(3) NUMBITS(1) [],
        MS_MODE OFFSET(4) NUMBITS(1) [
            Slave = 0,
            Master = 1,
        ],
        TRANS_START OFFSET(5) NUMBITS(1) [],
        TX_LSB_FIRST OFFSET(6) NUMBITS(1) [],
        RX_LSB_FIRST OFFSET(7) NUMBITS(1) [],
        CLK_EN OFFSET(8) NUMBITS(1) [],
        ARBITRATION_EN OFFSET(9) NUMBITS(1) [],
        FSM_RST OFFSET(10) NUMBITS(1) [],
        CONF_UPGATE OFFSET(11) NUMBITS(1) [],
        SLV_TX_AUTO_START_EN OFFSET(12) NUMBITS(1) [],
        ADDR_10BIT_RW_CHECK_EN OFFSET(13) NUMBITS(1) [],
        ADDR_BROADCASTING_EN OFFSET(14) NUMBITS(1) [],
    ],

    pub SR [
        RESP_REC OFFSET(0) NUMBITS(1) [],
        SLAVE_RW OFFSET(1) NUMBITS(1) [],
        ARB_LOST OFFSET(3) NUMBITS(1) [],
        BUS_BUSY OFFSET(4) NUMBITS(1) [],
        SLAVE_ADDRESSED OFFSET(5) NUMBITS(1) [],
        RXFIFO_CNT OFFSET(8) NUMBITS(6) [],
        STRETCH_CAUSE OFFSET(14) NUMBITS(2) [],
        TXFIFO_CNT OFFSET(18) NUMBITS(6) [],
        SCL_MAIN_STATE_LAST OFFSET(24) NUMBITS(3) [],
        SCL_STATE_LAST OFFSET(28) NUMBITS(3) [],
    ],

    pub TO [
        TIME_OUT_VALUE OFFSET(0) NUMBITS(5) [],
        TIME_OUT_EN OFFSET(5) NUMBITS(1) [],
    ],

    pub SLAVE_ADDR [
        SLAVE_ADDR OFFSET(0) NUMBITS(15) [],
        ADDR_10BIT_EN OFFSET(31) NUMBITS(1) [],
    ],

    pub FIFO_ST [
        RXFIFO_RADDR OFFSET(0) NUMBITS(5) [],
        RXFIFO_WADDR OFFSET(5) NUMBITS(5) [],
        TXFIFO_RADDR OFFSET(10) NUMBITS(5) [],
        TXFIFO_WADDR OFFSET(15) NUMBITS(5) [],
        SLAVE_RW_POINT OFFSET(22) NUMBITS(8) [],
    ],

    pub FIFO_CONF [
        RXFIFO_WM_THRHD OFFSET(0) NUMBITS(5) [],
        TXFIFO_WM_THRHD OFFSET(5) NUMBITS(5) [],
        NONFIFO_EN OFFSET(10) NUMBITS(1) [],
        FIFO_ADDR_CFG_EN OFFSET(11) NUMBITS(1) [],
        RX_FIFO_RST OFFSET(12) NUMBITS(1) [],
        TX_FIFO_RST OFFSET(13) NUMBITS(1) [],
        FIFO_PRT_EN OFFSET(14) NUMBITS(1) [],
    ],

    pub DATA [
        FIFO_RDATA OFFSET(0) NUMBITS(8) [],
    ],

    pub INTERRUPT [
        RXFIFO_WM OFFSET(0) NUMBITS(1) [],
        TXFIFO_WM OFFSET(1) NUMBITS(1) [],
        RXFIFO_OVF OFFSET(2) NUMBITS(1) [],
        END_DETECT OFFSET(3) NUMBITS(1) [],
        BYTE_TRANS_DONE OFFSET(4) NUMBITS(1) [],
        ARBITRATION_LOST OFFSET(5) NUMBITS(1) [],
        MST_TXFIFO_UDF OFFSET(6) NUMBITS(1) [],
        TRANS_COMPLETE OFFSET(7) NUMBITS(1) [],
        TIME_OUT OFFSET(8) NUMBITS(1) [],
        TRANS_START OFFSET(9) NUMBITS(1) [],
        NACK OFFSET(10) NUMBITS(1) [],
        TXFIFO_OVF OFFSET(11) NUMBITS(1) [],
        RXFIFO_UDF OFFSET(12) NUMBITS(1) [],
        SCL_ST_TO OFFSET(13) NUMBITS(1) [],
        SCL_MAIN_ST_TO OFFSET(14) NUMBITS(1) [],
        DET_START OFFSET(15) NUMBITS(1) [],
        SLAVE_STRETCH OFFSET(16) NUMBITS(1) [],
        GENERAL_CALL OFFSET(17) NUMBITS(1) [],
    ],

    pub SDA_HOLD [
        SDA_HOLD_TIME OFFSET(0) NUMBITS(9) [],
    ],

    pub SDA_SAMPLE [
        SDA_SAMPLE_TIME OFFSET(0) NUMBITS(9) [],
    ],

    pub SCL_HIGH_PERIOD [
        SCL_HIGH_PERIOD OFFSET(0) NUMBITS(9) [],
        SCL_WAIT_HIGH_PERIOD OFFSET(9) NUMBITS(7) [],
    ],

    pub SCL_START_HOLD [
        SCL_START_HOLD_TIME OFFSET(0) NUMBITS(9) [],
    ],

    pub SCL_RSTART_SETUP [
        SCL_RSTART_SETUP_TIME OFFSET(0) NUMBITS(9) [],
    ],

    pub SCL_STOP_HOLD [
        SCL_STOP_HOLD_TIME OFFSET(0) NUMBITS(9) [],
    ],

    pub SCL_STOP_SETUP [
        SCL_STOP_SETUP_TIME OFFSET(0) NUMBITS(9) [],
    ],

    pub FILTER_CFG [
        SCL_FILTER_THRES OFFSET(0) NUMBITS(4) [],
        SDA_FILTER_THRES OFFSET(4) NUMBITS(4) [],
        SCL_FILTER_EN OFFSET(8) NUMBITS(1) [],
        SDA_FILTER_EN OFFSET(9) NUMBITS(1) [],
    ],

    pub CLK_CONF [
        SCLK_DIV_NUM OFFSET(0) NUMBITS(8) [],
        SCLK_DIV_A OFFSET(8) NUMBITS(6) [],
        SCLK_DIV_B OFFSET(14) NUMBITS(6) [],
        SCLK_SEL OFFSET(20) NUMBITS(1) [],
        SCLK_ACTIVE OFFSET(21) NUMBITS(1) [],
    ],

    pub COMD [
        BYTE_NUM OFFSET(0) NUMBITS(8) [],
        ACK_CHECK_EN OFFSET(8) NUMBITS(1) [],
        ACK_EXP OFFSET(9) NUMBITS(1) [],
        ACK_VALUE OFFSET(10) NUMBITS(1) [],
        OPCODE OFFSET(11) NUMBITS(3) [
            Write = 1,
            Stop = 2,
            Read = 3,
            End = 4,
            Rstart = 6,
        ],
        COMMAND_DONE OFFSET(31) NUMBITS(1) [],
    ],

    pub SCL_ST_TIME_OUT [
        SCL_ST_TO OFFSET(0) NUMBITS(5) [],
    ],

    pub SCL_MAIN_ST_TIME_OUT [
        SCL_MAIN_ST_TO OFFSET(0) NUMBITS(5) [],
    ],

    pub SCL_SP_CONF [
        SCL_RST_SLV_EN OFFSET(0) NUMBITS(1) [],
        SCL_RST_SLV_NUM OFFSET(1) NUMBITS(5) [],
        SCL_PD_EN OFFSET(6) NUMBITS(1) [],
        SDA_PD_EN OFFSET(7) NUMBITS(1) [],
    ],

    pub SCL_STRETCH_CONF [
        STRETCH_PROTECT_NUM OFFSET(0) NUMBITS(10) [],
        SLAVE_SCL_STRETCH_EN OFFSET(10) NUMBITS(1) [],
        SLAVE_SCL_STRETCH_CLR OFFSET(11) NUMBITS(1) [],
        SLAVE_BYTE_ACK_CTL_EN OFFSET(12) NUMBITS(1) [],
        SLAVE_BYTE_ACK_LVL OFFSET(13) NUMBITS(1) [],
    ],

    pub PERIP_CLK_EN0 [
        I2C_EXT0_CLK_EN OFFSET(7) NUMBITS(1) [],
    ],

    pub PERIP_RST_EN0 [
        I2C_EXT0_RST OFFSET(7) NUMBITS(1) [],
    ],
];

register_structs! {
    SystemRegisters {
        (0x00 => _reserved0),
        (0x10 => perip_clk_en0: ReadWrite<u32, PERIP_CLK_EN0::Register>),
        (0x14 => _reserved1),
        (0x18 => perip_rst_en0: ReadWrite<u32, PERIP_RST_EN0::Register>),
        (0x1C => @END),
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Direction {
    Idle,
    Write,
    Read,
}

struct TransactionState {
    address: u8,
    baudrate: u32,
    direction: Direction,
    error_status: u32,
}

impl TransactionState {
    const fn new() -> Self {
        Self {
            address: 0,
            baudrate: 0,
            direction: Direction::Idle,
            error_status: 0,
        }
    }
}

struct Timing {
    divider: u32,
    scl_low_period: u32,
    scl_high_period: u32,
    scl_wait_high_period: u32,
    sda_hold_time: u32,
    sda_sample_time: u32,
    scl_setup_time: u32,
    scl_hold_time: u32,
}

fn calculate_timing(source_clk: u32, baudrate: u32) -> blueos_hal::err::Result<Timing> {
    if source_clk == 0 || baudrate == 0 || baudrate > 1_000_000 {
        return Err(blueos_hal::err::HalError::InvalidParam);
    }

    let divider = source_clk as u64 / (baudrate as u64 * 1024) + 1;
    if divider == 0 || divider > 256 {
        return Err(blueos_hal::err::HalError::InvalidParam);
    }

    let sclk = source_clk / divider as u32;
    let half_cycle = sclk / baudrate / 2;
    if half_cycle < 4 {
        return Err(blueos_hal::err::HalError::InvalidParam);
    }

    let scl_wait_high_period = if baudrate >= 80_000 {
        half_cycle / 2 - 2
    } else {
        half_cycle / 4
    };
    let scl_high_period = half_cycle - scl_wait_high_period;

    let timing = Timing {
        divider: divider as u32 - 1,
        scl_low_period: half_cycle - 1,
        scl_high_period,
        scl_wait_high_period,
        sda_hold_time: half_cycle / 4 - 1,
        sda_sample_time: half_cycle / 2 - 1,
        scl_setup_time: half_cycle - 1,
        scl_hold_time: half_cycle - 1,
    };

    if timing.scl_low_period > 0x1ff
        || timing.scl_high_period > 0x1ff
        || timing.scl_wait_high_period > 0x7f
        || timing.sda_hold_time > 0x1ff
        || timing.sda_sample_time > 0x1ff
        || timing.scl_setup_time > 0x1ff
        || timing.scl_hold_time > 0x1ff
    {
        return Err(blueos_hal::err::HalError::InvalidParam);
    }

    Ok(timing)
}

/// ESP32-C3 I2C master controller.
pub struct Esp32I2c {
    registers: StaticRef<I2cRegisters>,
    system_registers: StaticRef<SystemRegisters>,
    source_clk: u32,
    state: UnsafeCell<TransactionState>,
}

impl Esp32I2c {
    pub const fn new(base: usize, system_base: usize, source_clk: u32) -> Self {
        Self {
            registers: unsafe { StaticRef::new(base as *const I2cRegisters) },
            system_registers: unsafe { StaticRef::new(system_base as *const SystemRegisters) },
            source_clk,
            state: UnsafeCell::new(TransactionState::new()),
        }
    }

    fn state(&self) -> &mut TransactionState {
        unsafe { &mut *self.state.get() }
    }

    fn update_registers(&self) {
        self.registers.ctr.modify(CTR::CONF_UPGATE::SET);
    }

    fn reset_commands(&self) {
        for command in self.registers.comd.iter() {
            command.set(0);
        }
    }

    fn reset_fifo(&self) {
        self.registers
            .fifo_conf
            .modify(FIFO_CONF::RX_FIFO_RST::SET + FIFO_CONF::TX_FIFO_RST::SET);
        self.registers
            .fifo_conf
            .modify(FIFO_CONF::RX_FIFO_RST::CLEAR + FIFO_CONF::TX_FIFO_RST::CLEAR);
        self.update_registers();
    }

    fn clear_interrupts(&self) {
        self.registers.int_clr.set(ALL_INTERRUPTS);
    }

    fn prepare_segment(&self) {
        self.clear_interrupts();
        self.reset_fifo();
        self.reset_commands();
    }

    fn raw_error_status(&self) -> u32 {
        self.registers.int_raw.get() & ERROR_INTERRUPTS
    }

    fn latch_error(&self, error: u32) {
        let state = self.state();
        state.error_status |= error;
        state.direction = Direction::Idle;
    }

    fn recover_after_error(&self, error: u32) {
        let state = self.state();
        let address = state.address;
        let baudrate = state.baudrate;

        if baudrate != 0 {
            let _ = self.configure(&super::I2cConfig { baudrate });
        }

        let state = self.state();
        state.address = address;
        state.baudrate = baudrate;
        state.direction = Direction::Idle;
        state.error_status |= error;
    }

    fn map_error(error: u32) -> blueos_hal::err::HalError {
        if error & (1 << 10) != 0 {
            blueos_hal::err::HalError::NoAck
        } else if error & ((1 << 8) | (1 << 13) | (1 << 14) | SOFTWARE_TIMEOUT) != 0 {
            blueos_hal::err::HalError::Timeout
        } else {
            blueos_hal::err::HalError::Fail
        }
    }

    fn pending_error(&self) -> blueos_hal::err::Result<()> {
        let error = self.state().error_status | self.raw_error_status();
        if error == 0 {
            Ok(())
        } else {
            self.latch_error(error);
            Err(Self::map_error(error))
        }
    }

    fn wait_for_completion(&self, stop: bool) -> blueos_hal::err::Result<()> {
        let done = if stop { 1 << 7 } else { 1 << 3 };

        for _ in 0..POLL_LIMIT {
            let interrupts = self.registers.int_raw.get();
            let error = interrupts & ERROR_INTERRUPTS;
            if error != 0 {
                self.clear_interrupts();
                self.recover_after_error(error);
                return Err(Self::map_error(error));
            }
            if interrupts & done != 0 {
                self.clear_interrupts();
                return Ok(());
            }
            core::hint::spin_loop();
        }

        self.recover_after_error(SOFTWARE_TIMEOUT);
        Err(blueos_hal::err::HalError::Timeout)
    }

    fn write_fifo(&self, byte: u8) {
        self.registers.data.write(DATA::FIFO_RDATA.val(byte as u32));
    }

    fn start_transmission(&self) {
        self.update_registers();
        self.registers.ctr.modify(CTR::TRANS_START::SET);
    }

    fn append_end(&self, slot: usize, start: bool, stop: bool) {
        if stop {
            self.registers.comd[slot].write(COMD::OPCODE::Stop);
            if !start {
                self.registers.comd[slot + 1].write(COMD::OPCODE::End);
            }
        } else {
            self.registers.comd[slot].write(COMD::OPCODE::End);
        }
    }

    fn write_byte(&self, byte: u8, stop: bool) -> blueos_hal::err::Result<()> {
        self.pending_error()?;

        let state = self.state();
        let address = state.address;
        let start = state.direction != Direction::Write;

        self.prepare_segment();
        let mut slot = 0;
        if start {
            self.registers.comd[slot].write(COMD::OPCODE::Rstart);
            slot += 1;
            self.write_fifo(address << 1);
        }
        self.write_fifo(byte);

        self.registers.comd[slot].write(
            COMD::BYTE_NUM.val(if start { 2 } else { 1 })
                + COMD::ACK_CHECK_EN::SET
                + COMD::ACK_EXP::CLEAR
                + COMD::OPCODE::Write,
        );
        slot += 1;
        self.append_end(slot, start, stop);
        self.start_transmission();
        self.wait_for_completion(stop)?;

        self.state().direction = if stop {
            Direction::Idle
        } else {
            Direction::Write
        };
        Ok(())
    }

    fn read_byte(&self, stop: bool) -> blueos_hal::err::Result<u8> {
        self.pending_error()?;

        let state = self.state();
        let address = state.address;
        let start = state.direction != Direction::Read;

        self.prepare_segment();
        let mut slot = 0;
        if start {
            self.registers.comd[slot].write(COMD::OPCODE::Rstart);
            slot += 1;
            self.write_fifo((address << 1) | 1);
            self.registers.comd[slot].write(
                COMD::BYTE_NUM.val(1)
                    + COMD::ACK_CHECK_EN::SET
                    + COMD::ACK_EXP::CLEAR
                    + COMD::OPCODE::Write,
            );
            slot += 1;
        }

        self.registers.comd[slot].write(
            COMD::BYTE_NUM.val(1)
                + if stop {
                    COMD::ACK_VALUE::SET
                } else {
                    COMD::ACK_VALUE::CLEAR
                }
                + COMD::OPCODE::Read,
        );
        slot += 1;
        self.append_end(slot, start, stop);
        self.start_transmission();
        self.wait_for_completion(stop)?;

        if self.registers.sr.read(SR::RXFIFO_CNT) == 0 {
            self.recover_after_error(1 << 12);
            return Err(blueos_hal::err::HalError::NoData);
        }
        let byte = self.registers.data.read(DATA::FIFO_RDATA) as u8;
        self.state().direction = if stop {
            Direction::Idle
        } else {
            Direction::Read
        };
        Ok(byte)
    }

    fn configure_timing(&self, baudrate: u32) -> blueos_hal::err::Result<()> {
        let timing = calculate_timing(self.source_clk, baudrate)?;

        self.registers.clk_conf.write(
            CLK_CONF::SCLK_DIV_NUM.val(timing.divider)
                + CLK_CONF::SCLK_SEL::CLEAR
                + CLK_CONF::SCLK_ACTIVE::SET,
        );
        self.registers
            .scl_low_period
            .write(SCL_LOW_PERIOD::SCL_LOW_PERIOD.val(timing.scl_low_period));
        self.registers.scl_high_period.write(
            SCL_HIGH_PERIOD::SCL_HIGH_PERIOD.val(timing.scl_high_period)
                + SCL_HIGH_PERIOD::SCL_WAIT_HIGH_PERIOD.val(timing.scl_wait_high_period),
        );
        self.registers
            .sda_hold
            .write(SDA_HOLD::SDA_HOLD_TIME.val(timing.sda_hold_time));
        self.registers
            .sda_sample
            .write(SDA_SAMPLE::SDA_SAMPLE_TIME.val(timing.sda_sample_time));
        self.registers
            .scl_rstart_setup
            .write(SCL_RSTART_SETUP::SCL_RSTART_SETUP_TIME.val(timing.scl_setup_time));
        self.registers
            .scl_stop_setup
            .write(SCL_STOP_SETUP::SCL_STOP_SETUP_TIME.val(timing.scl_setup_time));
        self.registers
            .scl_start_hold
            .write(SCL_START_HOLD::SCL_START_HOLD_TIME.val(timing.scl_hold_time));
        self.registers
            .scl_stop_hold
            .write(SCL_STOP_HOLD::SCL_STOP_HOLD_TIME.val(timing.scl_hold_time));
        Ok(())
    }
}

// The upper I2C bus layer serializes access to the controller.
unsafe impl Send for Esp32I2c {}
unsafe impl Sync for Esp32I2c {}

impl PlatPeri for Esp32I2c {
    fn enable(&self) {
        self.system_registers
            .perip_clk_en0
            .modify(PERIP_CLK_EN0::I2C_EXT0_CLK_EN::SET);
        self.system_registers
            .perip_rst_en0
            .modify(PERIP_RST_EN0::I2C_EXT0_RST::SET);
        self.system_registers
            .perip_rst_en0
            .modify(PERIP_RST_EN0::I2C_EXT0_RST::CLEAR);
        self.registers.ctr.modify(CTR::CLK_EN::SET);
    }

    fn disable(&self) {
        self.registers.ctr.modify(CTR::CLK_EN::CLEAR);
        self.system_registers
            .perip_clk_en0
            .modify(PERIP_CLK_EN0::I2C_EXT0_CLK_EN::CLEAR);
    }
}

impl Configuration<super::I2cConfig> for Esp32I2c {
    type Target = ();

    fn configure(&self, config: &super::I2cConfig) -> blueos_hal::err::Result<Self::Target> {
        self.enable();

        self.registers.ctr.write(
            // Match esp-hal/ESP-IDF: use direct peripheral output together with
            // GPIO_PINn_PAD_DRIVER=open-drain on SDA and SCL.
            CTR::SDA_FORCE_OUT::SET
                + CTR::SCL_FORCE_OUT::SET
                + CTR::MS_MODE::Master
                + CTR::TX_LSB_FIRST::CLEAR
                + CTR::RX_LSB_FIRST::CLEAR
                + CTR::ARBITRATION_EN::CLEAR
                + CTR::CLK_EN::SET,
        );
        self.registers.filter_cfg.write(
            FILTER_CFG::SCL_FILTER_THRES.val(7)
                + FILTER_CFG::SDA_FILTER_THRES.val(7)
                + FILTER_CFG::SCL_FILTER_EN::SET
                + FILTER_CFG::SDA_FILTER_EN::SET,
        );
        self.configure_timing(config.baudrate)?;
        self.registers
            .to
            .write(TO::TIME_OUT_VALUE.val(1) + TO::TIME_OUT_EN::CLEAR);
        self.registers
            .scl_st_time_out
            .write(SCL_ST_TIME_OUT::SCL_ST_TO.val(23));
        self.registers
            .scl_main_st_time_out
            .write(SCL_MAIN_ST_TIME_OUT::SCL_MAIN_ST_TO.val(23));
        self.registers.int_ena.set(0);
        self.enable_fifo(1)?;
        self.reset_commands();
        self.clear_interrupts();
        self.update_registers();
        let state = self.state();
        state.baudrate = config.baudrate;
        state.direction = Direction::Idle;
        state.error_status = 0;
        Ok(())
    }
}

impl HasFifo for Esp32I2c {
    fn enable_fifo(&self, num: u8) -> blueos_hal::err::Result<()> {
        if num > 31 {
            return Err(blueos_hal::err::HalError::InvalidParam);
        }

        self.registers.fifo_conf.write(
            FIFO_CONF::RXFIFO_WM_THRHD.val(num as u32)
                + FIFO_CONF::TXFIFO_WM_THRHD.val(num as u32)
                + FIFO_CONF::NONFIFO_EN::CLEAR
                + FIFO_CONF::RX_FIFO_RST::SET
                + FIFO_CONF::TX_FIFO_RST::SET
                + FIFO_CONF::FIFO_PRT_EN::SET,
        );
        self.registers
            .fifo_conf
            .modify(FIFO_CONF::RX_FIFO_RST::CLEAR + FIFO_CONF::TX_FIFO_RST::CLEAR);
        self.update_registers();
        Ok(())
    }

    fn is_tx_fifo_full(&self) -> bool {
        self.get_error_status() != 0 || self.registers.sr.read(SR::TXFIFO_CNT) >= I2C_FIFO_SIZE
    }

    fn is_rx_fifo_empty(&self) -> bool {
        self.registers.sr.read(SR::RXFIFO_CNT) == 0
    }

    fn flush_tx_fifo(&self) {
        self.reset_fifo();
    }
}

impl Has8bitDataReg for Esp32I2c {
    fn read_data8(&self) -> blueos_hal::err::Result<u8> {
        self.read_byte(false)
    }

    fn write_data8(&self, data: u8) {
        let _ = self.write_byte(data, false);
    }

    fn is_data_ready(&self) -> bool {
        !self.is_rx_fifo_empty()
    }
}

impl blueos_hal::i2c::I2c<super::I2cConfig, ()> for Esp32I2c {
    fn set_address(&self, address: u16) -> blueos_hal::err::Result<()> {
        if address > 0x7f {
            return Err(blueos_hal::err::HalError::InvalidParam);
        }
        if self.state().direction != Direction::Idle {
            self.release_bus()?;
        }

        self.clear_interrupts();
        let state = self.state();
        state.address = address as u8;
        state.direction = Direction::Idle;
        state.error_status = 0;
        Ok(())
    }

    fn send_byte_with_stop(&self, byte: u8) -> blueos_hal::err::Result<()> {
        self.write_byte(byte, true)
    }

    fn read_byte_with_stop(&self) -> blueos_hal::err::Result<u8> {
        self.read_byte(true)
    }

    fn release_bus(&self) -> blueos_hal::err::Result<()> {
        if self.state().direction == Direction::Idle {
            self.clear_error_status();
            return Ok(());
        }

        self.prepare_segment();
        self.registers.comd[0].write(COMD::OPCODE::Stop);
        self.registers.comd[1].write(COMD::OPCODE::End);
        self.start_transmission();
        let result = self.wait_for_completion(true);
        self.state().direction = Direction::Idle;
        if result.is_ok() {
            self.clear_error_status();
        }
        result
    }
}

impl HasErrorStatusReg for Esp32I2c {
    type ErrorStatusType = u32;

    fn get_error_status(&self) -> Self::ErrorStatusType {
        let error = self.raw_error_status();
        if error != 0 {
            self.latch_error(error);
        }
        self.state().error_status
    }

    fn clear_error_status(&self) {
        self.clear_interrupts();
        let state = self.state();
        state.error_status = 0;
        state.direction = Direction::Idle;
    }
}
