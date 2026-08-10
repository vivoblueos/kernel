// Copyright (c) 2026 vivo Mobile Communication Co., Ltd.
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

//! ESP32-C3 GPSPI2 (SPI2) register-level driver.

use crate::spi::{SpiBitOrder, SpiConfig, SpiPhase, SpiPolarity};
use blueos_hal::{Configuration, PlatPeri};
use tock_registers::{
    interfaces::{ReadWriteable, Readable, Writeable},
    register_bitfields, register_structs,
    registers::ReadWrite,
};

const SPI2_DATA_BUF_SIZE: usize = 64;

// Pad byte for full-duplex reads where read length exceeds write length.
const EMPTY_WRITE_PAD: u8 = 0x00;

register_bitfields! [
    u32,

    pub CMD [
        USR OFFSET(24) NUMBITS(1) [],
        UPDATE OFFSET(23) NUMBITS(1) [],
    ],

    pub CTRL [
        RD_BIT_ORDER OFFSET(25) NUMBITS(1) [
            MsbFirst = 0,
            LsbFirst = 1,
        ],
        WR_BIT_ORDER OFFSET(26) NUMBITS(1) [
            MsbFirst = 0,
            LsbFirst = 1,
        ],
    ],

    pub CLOCK [
        CLKCNT_L OFFSET(0) NUMBITS(6) [],
        CLKCNT_H OFFSET(6) NUMBITS(6) [],
        CLKCNT_N OFFSET(12) NUMBITS(6) [],
        CLKDIV_PRE OFFSET(18) NUMBITS(4) [],
        CLK_EQU_SYSCLK OFFSET(31) NUMBITS(1) [],
    ],

    pub USER [
        DOUTDIN OFFSET(0) NUMBITS(1) [
            HalfDuplex = 0,
            FullDuplex = 1,
        ],
        CK_OUT_EDGE OFFSET(9) NUMBITS(1) [
            LeadingEdge = 0,
            TrailingEdge = 1,
        ],
        USR_MOSI OFFSET(27) NUMBITS(1) [],
        USR_MISO OFFSET(28) NUMBITS(1) [],
        USR_DUMMY OFFSET(29) NUMBITS(1) [],
        USR_ADDR OFFSET(30) NUMBITS(1) [],
        USR_COMMAND OFFSET(31) NUMBITS(1) [],
    ],

    pub USER1 [
        USR_DUMMY_CYCLELEN OFFSET(0) NUMBITS(8) [],
        USR_ADDR_BITLEN OFFSET(27) NUMBITS(5) [],
    ],

    pub USER2 [
        USR_COMMAND_VALUE OFFSET(0) NUMBITS(16) [],
        USR_COMMAND_BITLEN OFFSET(28) NUMBITS(4) [],
    ],

    pub MS_DLEN [
        MS_DATA_BITLEN OFFSET(0) NUMBITS(18) [],
    ],

    pub MISC [
        CS0_DIS OFFSET(0) NUMBITS(1) [
            Enabled = 0,
            Disabled = 1,
        ],
        CS1_DIS OFFSET(1) NUMBITS(1) [
            Enabled = 0,
            Disabled = 1,
        ],
        CS2_DIS OFFSET(2) NUMBITS(1) [
            Enabled = 0,
            Disabled = 1,
        ],
        CS3_DIS OFFSET(3) NUMBITS(1) [
            Enabled = 0,
            Disabled = 1,
        ],
        CS4_DIS OFFSET(4) NUMBITS(1) [
            Enabled = 0,
            Disabled = 1,
        ],
        CS5_DIS OFFSET(5) NUMBITS(1) [
            Enabled = 0,
            Disabled = 1,
        ],
        CK_IDLE_EDGE OFFSET(29) NUMBITS(1) [
            Low = 0,
            High = 1,
        ],
        CS_KEEP_ACTIVE OFFSET(30) NUMBITS(1) [],
    ],

    pub SLAVE [
        CLK_MODE OFFSET(0) NUMBITS(2) [],
        CLK_MODE_13 OFFSET(2) NUMBITS(1) [],
        SLAVE_MODE OFFSET(26) NUMBITS(1) [
            Master = 0,
            Slave = 1,
        ],
        SOFT_RESET OFFSET(27) NUMBITS(1) [],
    ],

    pub CLK_GATE [
        CLK_EN OFFSET(0) NUMBITS(1) [],
        MST_CLK_ACTIVE OFFSET(1) NUMBITS(1) [],
        MST_CLK_SEL OFFSET(2) NUMBITS(1) [
            XtalClock = 0,
            PllClock = 1,
        ],
    ],

    pub DMA_CONF [
        DMA_RX_ENA OFFSET(27) NUMBITS(1) [],
        DMA_TX_ENA OFFSET(28) NUMBITS(1) [],
        RX_AFIFO_RST OFFSET(29) NUMBITS(1) [],
        BUF_AFIFO_RST OFFSET(30) NUMBITS(1) [],
    ],

    pub DMA_INT_RAW [
        TRANS_DONE OFFSET(12) NUMBITS(1) [],
    ],

    pub DMA_INT_CLR [
        TRANS_DONE OFFSET(12) NUMBITS(1) [],
    ],

    pub PERIP_CLK_EN0 [
        SPI2_CLK_EN OFFSET(6) NUMBITS(1) [
            Enabled = 1,
            Disabled = 0,
        ],
    ],

    pub PERIP_RST_EN0 [
        SPI2_RST OFFSET(6) NUMBITS(1) [
            NoReset = 0,
            Reset = 1,
        ],
    ],
];

register_structs! {
    Spi2Registers {
        (0x00 => cmd: ReadWrite<u32, CMD::Register>),
        (0x04 => addr: ReadWrite<u32>),
        (0x08 => ctrl: ReadWrite<u32, CTRL::Register>),
        (0x0C => clock: ReadWrite<u32, CLOCK::Register>),
        (0x10 => user: ReadWrite<u32, USER::Register>),
        (0x14 => user1: ReadWrite<u32, USER1::Register>),
        (0x18 => user2: ReadWrite<u32, USER2::Register>),
        (0x1C => ms_dlen: ReadWrite<u32, MS_DLEN::Register>),
        (0x20 => misc: ReadWrite<u32, MISC::Register>),
        (0x24 => din_mode: ReadWrite<u32>),
        (0x28 => din_num: ReadWrite<u32>),
        (0x2C => dout_mode: ReadWrite<u32>),
        (0x30 => dma_conf: ReadWrite<u32, DMA_CONF::Register>),
        (0x34 => dma_int_ena: ReadWrite<u32>),
        (0x38 => dma_int_clr: ReadWrite<u32, DMA_INT_CLR::Register>),
        (0x3C => dma_int_raw: ReadWrite<u32, DMA_INT_RAW::Register>),
        (0x40 => dma_int_st: ReadWrite<u32>),
        (0x44 => _reserved0),
        (0x98 => w0: ReadWrite<u32>),
        (0x9C => w1: ReadWrite<u32>),
        (0xA0 => w2: ReadWrite<u32>),
        (0xA4 => w3: ReadWrite<u32>),
        (0xA8 => w4: ReadWrite<u32>),
        (0xAC => w5: ReadWrite<u32>),
        (0xB0 => w6: ReadWrite<u32>),
        (0xB4 => w7: ReadWrite<u32>),
        (0xB8 => w8: ReadWrite<u32>),
        (0xBC => w9: ReadWrite<u32>),
        (0xC0 => w10: ReadWrite<u32>),
        (0xC4 => w11: ReadWrite<u32>),
        (0xC8 => w12: ReadWrite<u32>),
        (0xCC => w13: ReadWrite<u32>),
        (0xD0 => w14: ReadWrite<u32>),
        (0xD4 => w15: ReadWrite<u32>),
        (0xD8 => _reserved1),
        (0xE0 => slave: ReadWrite<u32, SLAVE::Register>),
        (0xE4 => slave1: ReadWrite<u32>),
        (0xE8 => clk_gate: ReadWrite<u32, CLK_GATE::Register>),
        (0xEC => _reserved2),
        (0xF0 => @END),
    }
}

// System registers for SPI2 clock gating and reset.
register_structs! {
    SystemRegisters {
        (0x00 => _reserved_sys0),
        (0x10 => perip_clk_en0: ReadWrite<u32, PERIP_CLK_EN0::Register>),
        (0x14 => _reserved_sys1),
        (0x18 => perip_rst_en0: ReadWrite<u32, PERIP_RST_EN0::Register>),
        (0x1C => @END),
    }
}

/// ESP32-C3 GPSPI2 (SPI2) peripheral, generic over register base and APB clock.
pub struct Esp32Spi2<const SPI_BASE: usize, const SYS_BASE: usize, const APB_HZ: u32> {}

unsafe impl<const SPI_BASE: usize, const SYS_BASE: usize, const APB_HZ: u32> Send
    for Esp32Spi2<SPI_BASE, SYS_BASE, APB_HZ>
{
}
unsafe impl<const SPI_BASE: usize, const SYS_BASE: usize, const APB_HZ: u32> Sync
    for Esp32Spi2<SPI_BASE, SYS_BASE, APB_HZ>
{
}

impl<const SPI_BASE: usize, const SYS_BASE: usize, const APB_HZ: u32>
    Esp32Spi2<SPI_BASE, SYS_BASE, APB_HZ>
{
    pub const fn new() -> Self {
        Self {}
    }

    fn spi_regs() -> &'static Spi2Registers {
        unsafe { &*(SPI_BASE as *const Spi2Registers) }
    }

    fn sys_regs() -> &'static SystemRegisters {
        unsafe { &*(SYS_BASE as *const SystemRegisters) }
    }

    fn write_buf(&self, data: &[u8]) {
        debug_assert!(data.len() <= SPI2_DATA_BUF_SIZE);
        let regs = Self::spi_regs();
        let words = data.chunks(4);
        for (i, chunk) in words.enumerate() {
            let mut word = 0u32;
            for (j, byte) in chunk.iter().enumerate() {
                word |= (*byte as u32) << (j * 8);
            }
            match i {
                0 => regs.w0.set(word),
                1 => regs.w1.set(word),
                2 => regs.w2.set(word),
                3 => regs.w3.set(word),
                4 => regs.w4.set(word),
                5 => regs.w5.set(word),
                6 => regs.w6.set(word),
                7 => regs.w7.set(word),
                8 => regs.w8.set(word),
                9 => regs.w9.set(word),
                10 => regs.w10.set(word),
                11 => regs.w11.set(word),
                12 => regs.w12.set(word),
                13 => regs.w13.set(word),
                14 => regs.w14.set(word),
                15 => regs.w15.set(word),
                _ => break,
            }
        }
    }

    fn read_buf(&self, data: &mut [u8]) {
        let regs = Self::spi_regs();
        let words = [
            regs.w0.get(),
            regs.w1.get(),
            regs.w2.get(),
            regs.w3.get(),
            regs.w4.get(),
            regs.w5.get(),
            regs.w6.get(),
            regs.w7.get(),
            regs.w8.get(),
            regs.w9.get(),
            regs.w10.get(),
            regs.w11.get(),
            regs.w12.get(),
            regs.w13.get(),
            regs.w14.get(),
            regs.w15.get(),
        ];
        for (i, byte) in data.iter_mut().enumerate() {
            let word_idx = i / 4;
            let byte_idx = i % 4;
            if word_idx < words.len() {
                *byte = ((words[word_idx] >> (byte_idx * 8)) & 0xFF) as u8;
            }
        }
    }

    fn apply_config(&self) {
        let regs = Self::spi_regs();
        regs.cmd.write(CMD::UPDATE.val(1));
        while regs.cmd.is_set(CMD::UPDATE) {}
    }

    // AFIFO reset is a SET-then-CLEAR pulse.
    fn reset_tx_fifo(&self) {
        let regs = Self::spi_regs();
        regs.dma_conf.modify(DMA_CONF::BUF_AFIFO_RST::SET);
        regs.dma_conf.modify(DMA_CONF::BUF_AFIFO_RST::CLEAR);
    }

    fn reset_rx_fifo(&self) {
        let regs = Self::spi_regs();
        regs.dma_conf.modify(DMA_CONF::RX_AFIFO_RST::SET);
        regs.dma_conf.modify(DMA_CONF::RX_AFIFO_RST::CLEAR);
    }

    fn reset_tx_rx_fifo(&self) {
        let regs = Self::spi_regs();
        regs.dma_conf
            .modify(DMA_CONF::BUF_AFIFO_RST::SET + DMA_CONF::RX_AFIFO_RST::SET);
        regs.dma_conf
            .modify(DMA_CONF::BUF_AFIFO_RST::CLEAR + DMA_CONF::RX_AFIFO_RST::CLEAR);
    }

    fn start_transfer(&self) {
        let regs = Self::spi_regs();
        // Sync shadow registers, clear stale TRANS_DONE, then start (USR self-clears).
        regs.cmd.modify(CMD::UPDATE.val(1));
        while regs.cmd.is_set(CMD::UPDATE) {}
        regs.dma_int_clr.write(DMA_INT_CLR::TRANS_DONE::SET);
        regs.cmd.modify(CMD::USR.val(1));
        while regs.cmd.is_set(CMD::USR) {}
    }

    fn wait_done(&self) {
        // No DMA in use; with DMA, poll dma_int_raw TRANS_DONE then clear it via dma_int_clr.
    }

    fn configure_clock(&self, baudrate: u32) -> blueos_hal::err::Result<()> {
        let regs = Self::spi_regs();
        if baudrate >= APB_HZ {
            regs.clock.write(CLOCK::CLK_EQU_SYSCLK.val(1));
            return Ok(());
        }

        // f_spi = f_apb / ((pre+1) * (n+1)), minimum divisor = 2; prefer larger n for duty cycle.
        let divisor = (APB_HZ / baudrate).max(2);

        let mut best_pre = 0u32;
        let mut best_n_plus_one = 0u32;
        for pre in 0..16u32 {
            let n_plus_one = divisor / (pre + 1);
            if n_plus_one >= 2 && n_plus_one <= 64 {
                let actual = (pre + 1) * n_plus_one;
                if actual == divisor {
                    best_pre = pre;
                    best_n_plus_one = n_plus_one;
                    break;
                }
                if best_n_plus_one == 0 {
                    best_pre = pre;
                    best_n_plus_one = n_plus_one;
                }
            }
        }

        // No valid combination: minimum is APB/1024 (~78kHz).
        if best_n_plus_one == 0 {
            return Err(blueos_hal::err::HalError::NotSupport);
        }

        let n = best_n_plus_one - 1;
        let h = ((best_n_plus_one / 2).max(1) - 1) as u32;
        regs.clock.write(
            CLOCK::CLKCNT_L.val(n as u32)
                + CLOCK::CLKCNT_H.val(h)
                + CLOCK::CLKCNT_N.val(n as u32)
                + CLOCK::CLKDIV_PRE.val(best_pre as u32)
                + CLOCK::CLK_EQU_SYSCLK.val(0),
        );
        Ok(())
    }

    fn do_half_duplex_write(&self, data: &[u8]) -> blueos_hal::err::Result<()> {
        if data.is_empty() {
            return Ok(());
        }
        let regs = Self::spi_regs();

        regs.user.modify(
            USER::DOUTDIN.val(0)
                + USER::USR_MOSI::SET
                + USER::USR_MISO::CLEAR
                + USER::USR_COMMAND::CLEAR
                + USER::USR_ADDR::CLEAR
                + USER::USR_DUMMY::CLEAR,
        );

        for chunk in data.chunks(SPI2_DATA_BUF_SIZE) {
            self.reset_tx_fifo();
            regs.ms_dlen
                .write(MS_DLEN::MS_DATA_BITLEN.val((chunk.len() as u32 * 8 - 1)));
            self.write_buf(chunk);
            self.start_transfer();
            self.wait_done();
        }
        Ok(())
    }

    fn do_half_duplex_read(&self, data: &mut [u8]) -> blueos_hal::err::Result<()> {
        if data.is_empty() {
            return Ok(());
        }
        let regs = Self::spi_regs();

        // Full-duplex dummy read (write 0x00 while reading): half-duplex MISO-only
        // returned misaligned data on real hardware.
        regs.user.modify(
            USER::DOUTDIN.val(1)
                + USER::USR_MOSI::SET
                + USER::USR_MISO::SET
                + USER::USR_COMMAND::CLEAR
                + USER::USR_ADDR::CLEAR
                + USER::USR_DUMMY::CLEAR,
        );

        for chunk in data.chunks_mut(SPI2_DATA_BUF_SIZE) {
            self.reset_tx_rx_fifo();
            regs.ms_dlen
                .write(MS_DLEN::MS_DATA_BITLEN.val((chunk.len() as u32 * 8 - 1)));
            let dummy = [EMPTY_WRITE_PAD; SPI2_DATA_BUF_SIZE];
            self.write_buf(&dummy[..chunk.len()]);
            self.start_transfer();
            self.wait_done();
            self.read_buf(chunk);
        }
        Ok(())
    }

    fn do_full_duplex_transfer(
        &self,
        read: &mut [u8],
        write: &[u8],
    ) -> blueos_hal::err::Result<()> {
        if read.is_empty() && write.is_empty() {
            return Ok(());
        }
        let regs = Self::spi_regs();

        regs.user.modify(
            USER::DOUTDIN.val(1)
                + USER::USR_MOSI::SET
                + USER::USR_MISO::SET
                + USER::USR_COMMAND::CLEAR
                + USER::USR_ADDR::CLEAR
                + USER::USR_DUMMY::CLEAR,
        );

        // Independent read/write cursors; pad the shorter side with EMPTY_WRITE_PAD.
        let mut write_from = 0usize;
        let mut read_from = 0usize;
        loop {
            let write_inc = core::cmp::min(SPI2_DATA_BUF_SIZE, write.len() - write_from);
            let read_inc = core::cmp::min(SPI2_DATA_BUF_SIZE, read.len() - read_from);
            if write_inc == 0 && read_inc == 0 {
                break;
            }

            let this_len = write_inc.max(read_inc);
            self.reset_tx_rx_fifo();
            regs.ms_dlen
                .write(MS_DLEN::MS_DATA_BITLEN.val((this_len as u32 * 8 - 1)));

            if write_inc < read_inc {
                // Read more than we write: pad write side up to read_inc bytes.
                let mut buf = [EMPTY_WRITE_PAD; SPI2_DATA_BUF_SIZE];
                buf[..write_inc].copy_from_slice(&write[write_from..][..write_inc]);
                self.write_buf(&buf[..read_inc]);
            } else {
                self.write_buf(&write[write_from..][..write_inc]);
            }

            self.start_transfer();
            self.wait_done();

            if read_inc > 0 {
                let mut tmp = [0u8; SPI2_DATA_BUF_SIZE];
                self.read_buf(&mut tmp[..read_inc]);
                read[read_from..][..read_inc].copy_from_slice(&tmp[..read_inc]);
            }

            write_from += write_inc;
            read_from += read_inc;
        }
        Ok(())
    }
}

impl<const SPI_BASE: usize, const SYS_BASE: usize, const APB_HZ: u32> PlatPeri
    for Esp32Spi2<SPI_BASE, SYS_BASE, APB_HZ>
{
    fn enable(&self) {
        let sys = Self::sys_regs();
        sys.perip_clk_en0.modify(PERIP_CLK_EN0::SPI2_CLK_EN::SET);
        // Reset pulse; without it CMD::UPDATE may never clear.
        sys.perip_rst_en0.modify(PERIP_RST_EN0::SPI2_RST::SET);
        sys.perip_rst_en0.modify(PERIP_RST_EN0::SPI2_RST::CLEAR);

        let regs = Self::spi_regs();
        regs.clk_gate.write(
            CLK_GATE::CLK_EN.val(1)
                + CLK_GATE::MST_CLK_ACTIVE.val(1)
                + CLK_GATE::MST_CLK_SEL.val(1),
        );
    }

    fn disable(&self) {
        let regs = Self::spi_regs();
        regs.clk_gate.modify(CLK_GATE::MST_CLK_ACTIVE::CLEAR);
        let sys = Self::sys_regs();
        sys.perip_clk_en0.modify(PERIP_CLK_EN0::SPI2_CLK_EN::CLEAR);
    }
}

impl<const SPI_BASE: usize, const SYS_BASE: usize, const APB_HZ: u32> Configuration<SpiConfig>
    for Esp32Spi2<SPI_BASE, SYS_BASE, APB_HZ>
{
    type Target = ();

    fn configure(&self, config: &SpiConfig) -> blueos_hal::err::Result<Self::Target> {
        let regs = Self::spi_regs();

        // Ensure peripheral is enabled
        self.enable();

        // Master mode, soft reset first
        regs.slave
            .write(SLAVE::SLAVE_MODE.val(0) + SLAVE::SOFT_RESET.val(1));
        regs.slave.modify(SLAVE::SOFT_RESET::CLEAR);

        // No DMA, clear FIFOs
        regs.dma_conf
            .write(DMA_CONF::DMA_RX_ENA::CLEAR + DMA_CONF::DMA_TX_ENA::CLEAR);
        self.reset_tx_rx_fifo();

        // SPI mode from phase + polarity
        let ck_idle_edge = match config.polarity {
            SpiPolarity::Low => MISC::CK_IDLE_EDGE::Low,
            SpiPolarity::High => MISC::CK_IDLE_EDGE::High,
        };
        let ck_out_edge = match (config.polarity, config.phase) {
            (SpiPolarity::Low, SpiPhase::Phase0) => USER::CK_OUT_EDGE::LeadingEdge, // Mode 0
            (SpiPolarity::Low, SpiPhase::Phase1) => USER::CK_OUT_EDGE::TrailingEdge, // Mode 1
            (SpiPolarity::High, SpiPhase::Phase0) => USER::CK_OUT_EDGE::TrailingEdge, // Mode 2
            (SpiPolarity::High, SpiPhase::Phase1) => USER::CK_OUT_EDGE::LeadingEdge, // Mode 3
        };
        regs.misc.modify(ck_idle_edge);
        regs.user.modify(ck_out_edge);

        // Bit order
        let rd_bit_order = match config.bit_order {
            SpiBitOrder::MsbFirst => CTRL::RD_BIT_ORDER::MsbFirst,
            SpiBitOrder::LsbFirst => CTRL::RD_BIT_ORDER::LsbFirst,
        };
        let wr_bit_order = match config.bit_order {
            SpiBitOrder::MsbFirst => CTRL::WR_BIT_ORDER::MsbFirst,
            SpiBitOrder::LsbFirst => CTRL::WR_BIT_ORDER::LsbFirst,
        };
        regs.ctrl.modify(rd_bit_order + wr_bit_order);

        // Clock divider
        self.configure_clock(config.baudrate)?;

        // All HW CS lines disabled; CS managed by software GPIO via ExclusiveDevice
        regs.misc.modify(
            MISC::CS0_DIS.val(1)
                + MISC::CS1_DIS.val(1)
                + MISC::CS2_DIS.val(1)
                + MISC::CS3_DIS.val(1)
                + MISC::CS4_DIS.val(1)
                + MISC::CS5_DIS.val(1)
                + MISC::CS_KEEP_ACTIVE::CLEAR,
        );

        Ok(())
    }
}

impl<const SPI_BASE: usize, const SYS_BASE: usize, const APB_HZ: u32>
    blueos_hal::spi::Spi<SpiConfig, ()> for Esp32Spi2<SPI_BASE, SYS_BASE, APB_HZ>
{
    fn transfer(&self, read: &mut [u8], write: &[u8]) -> blueos_hal::err::Result<()> {
        self.do_full_duplex_transfer(read, write)
    }

    fn read(&self, buf: &mut [u8]) -> blueos_hal::err::Result<()> {
        self.do_half_duplex_read(buf)
    }

    fn write(&self, buf: &[u8]) -> blueos_hal::err::Result<()> {
        self.do_half_duplex_write(buf)
    }
}
