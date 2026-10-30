#[repr(C)]
#[cfg_attr(feature = "impl-register-debug", derive(Debug))]
#[doc = "Register block"]
pub struct RegisterBlock {
    pgm_data0: PGM_DATA0,
    pgm_data1: PGM_DATA1,
    pgm_data2: PGM_DATA2,
    pgm_data3: PGM_DATA3,
    pgm_data4: PGM_DATA4,
    pgm_data5: PGM_DATA5,
    pgm_data6: PGM_DATA6,
    pgm_data7: PGM_DATA7,
    pgm_check_value0: PGM_CHECK_VALUE0,
    pgm_check_value1: PGM_CHECK_VALUE1,
    pgm_check_value2: PGM_CHECK_VALUE2,
    rd_wr_dis: RD_WR_DIS,
    rd_repeat_data0: RD_REPEAT_DATA0,
    rd_repeat_data1: RD_REPEAT_DATA1,
    rd_repeat_data2: RD_REPEAT_DATA2,
    rd_repeat_data3: RD_REPEAT_DATA3,
    rd_repeat_data4: RD_REPEAT_DATA4,
    rd_mac_spi_sys_0: RD_MAC_SPI_SYS_0,
    rd_mac_spi_sys_1: RD_MAC_SPI_SYS_1,
    rd_mac_spi_sys_2: RD_MAC_SPI_SYS_2,
    rd_mac_spi_sys_3: RD_MAC_SPI_SYS_3,
    rd_mac_spi_sys_4: RD_MAC_SPI_SYS_4,
    rd_mac_spi_sys_5: RD_MAC_SPI_SYS_5,
    rd_sys_part1_data0: RD_SYS_PART1_DATA0,
    rd_sys_part1_data1: RD_SYS_PART1_DATA1,
    rd_sys_part1_data2: RD_SYS_PART1_DATA2,
    rd_sys_part1_data3: RD_SYS_PART1_DATA3,
    rd_sys_part1_data4: RD_SYS_PART1_DATA4,
    rd_sys_part1_data5: RD_SYS_PART1_DATA5,
    rd_sys_part1_data6: RD_SYS_PART1_DATA6,
    rd_sys_part1_data7: RD_SYS_PART1_DATA7,
    rd_usr_data0: RD_USR_DATA0,
    rd_usr_data1: RD_USR_DATA1,
    rd_usr_data2: RD_USR_DATA2,
    rd_usr_data3: RD_USR_DATA3,
    rd_usr_data4: RD_USR_DATA4,
    rd_usr_data5: RD_USR_DATA5,
    rd_usr_data6: RD_USR_DATA6,
    rd_usr_data7: RD_USR_DATA7,
    rd_key0_data0: RD_KEY0_DATA0,
    rd_key0_data1: RD_KEY0_DATA1,
    rd_key0_data2: RD_KEY0_DATA2,
    rd_key0_data3: RD_KEY0_DATA3,
    rd_key0_data4: RD_KEY0_DATA4,
    rd_key0_data5: RD_KEY0_DATA5,
    rd_key0_data6: RD_KEY0_DATA6,
    rd_key0_data7: RD_KEY0_DATA7,
    rd_key1_data0: RD_KEY1_DATA0,
    rd_key1_data1: RD_KEY1_DATA1,
    rd_key1_data2: RD_KEY1_DATA2,
    rd_key1_data3: RD_KEY1_DATA3,
    rd_key1_data4: RD_KEY1_DATA4,
    rd_key1_data5: RD_KEY1_DATA5,
    rd_key1_data6: RD_KEY1_DATA6,
    rd_key1_data7: RD_KEY1_DATA7,
    rd_key2_data0: RD_KEY2_DATA0,
    rd_key2_data1: RD_KEY2_DATA1,
    rd_key2_data2: RD_KEY2_DATA2,
    rd_key2_data3: RD_KEY2_DATA3,
    rd_key2_data4: RD_KEY2_DATA4,
    rd_key2_data5: RD_KEY2_DATA5,
    rd_key2_data6: RD_KEY2_DATA6,
    rd_key2_data7: RD_KEY2_DATA7,
    rd_key3_data0: RD_KEY3_DATA0,
    rd_key3_data1: RD_KEY3_DATA1,
    rd_key3_data2: RD_KEY3_DATA2,
    rd_key3_data3: RD_KEY3_DATA3,
    rd_key3_data4: RD_KEY3_DATA4,
    rd_key3_data5: RD_KEY3_DATA5,
    rd_key3_data6: RD_KEY3_DATA6,
    rd_key3_data7: RD_KEY3_DATA7,
    rd_key4_data0: RD_KEY4_DATA0,
    rd_key4_data1: RD_KEY4_DATA1,
    rd_key4_data2: RD_KEY4_DATA2,
    rd_key4_data3: RD_KEY4_DATA3,
    rd_key4_data4: RD_KEY4_DATA4,
    rd_key4_data5: RD_KEY4_DATA5,
    rd_key4_data6: RD_KEY4_DATA6,
    rd_key4_data7: RD_KEY4_DATA7,
    rd_key5_data0: RD_KEY5_DATA0,
    rd_key5_data1: RD_KEY5_DATA1,
    rd_key5_data2: RD_KEY5_DATA2,
    rd_key5_data3: RD_KEY5_DATA3,
    rd_key5_data4: RD_KEY5_DATA4,
    rd_key5_data5: RD_KEY5_DATA5,
    rd_key5_data6: RD_KEY5_DATA6,
    rd_key5_data7: RD_KEY5_DATA7,
    rd_sys_part2_data0: RD_SYS_PART2_DATA0,
    rd_sys_part2_data1: RD_SYS_PART2_DATA1,
    rd_sys_part2_data2: RD_SYS_PART2_DATA2,
    rd_sys_part2_data3: RD_SYS_PART2_DATA3,
    rd_sys_part2_data4: RD_SYS_PART2_DATA4,
    rd_sys_part2_data5: RD_SYS_PART2_DATA5,
    rd_sys_part2_data6: RD_SYS_PART2_DATA6,
    rd_sys_part2_data7: RD_SYS_PART2_DATA7,
    rd_repeat_err0: RD_REPEAT_ERR0,
    rd_repeat_err1: RD_REPEAT_ERR1,
    rd_repeat_err2: RD_REPEAT_ERR2,
    rd_repeat_err3: RD_REPEAT_ERR3,
    _reserved99: [u8; 0x04],
    rd_repeat_err4: RD_REPEAT_ERR4,
    _reserved100: [u8; 0x2c],
    rd_rs_err0: RD_RS_ERR0,
    rd_rs_err1: RD_RS_ERR1,
    clk: CLK,
    conf: CONF,
    status: STATUS,
    cmd: CMD,
    int_raw: INT_RAW,
    int_st: INT_ST,
    int_ena: INT_ENA,
    int_clr: INT_CLR,
    dac_conf: DAC_CONF,
    rd_tim_conf: RD_TIM_CONF,
    wr_tim_conf1: WR_TIM_CONF1,
    wr_tim_conf2: WR_TIM_CONF2,
    wr_tim_conf0_rs_bypass: WR_TIM_CONF0_RS_BYPASS,
    date: DATE,
}
impl RegisterBlock {
    #[doc = "0x00 - Register 0 that stores data to be programmed."]
    #[inline(always)]
    pub const fn pgm_data0(&self) -> &PGM_DATA0 {
        &self.pgm_data0
    }
    #[doc = "0x04 - Register 1 that stores data to be programmed."]
    #[inline(always)]
    pub const fn pgm_data1(&self) -> &PGM_DATA1 {
        &self.pgm_data1
    }
    #[doc = "0x08 - Register 2 that stores data to be programmed."]
    #[inline(always)]
    pub const fn pgm_data2(&self) -> &PGM_DATA2 {
        &self.pgm_data2
    }
    #[doc = "0x0c - Register 3 that stores data to be programmed."]
    #[inline(always)]
    pub const fn pgm_data3(&self) -> &PGM_DATA3 {
        &self.pgm_data3
    }
    #[doc = "0x10 - Register 4 that stores data to be programmed."]
    #[inline(always)]
    pub const fn pgm_data4(&self) -> &PGM_DATA4 {
        &self.pgm_data4
    }
    #[doc = "0x14 - Register 5 that stores data to be programmed."]
    #[inline(always)]
    pub const fn pgm_data5(&self) -> &PGM_DATA5 {
        &self.pgm_data5
    }
    #[doc = "0x18 - Register 6 that stores data to be programmed."]
    #[inline(always)]
    pub const fn pgm_data6(&self) -> &PGM_DATA6 {
        &self.pgm_data6
    }
    #[doc = "0x1c - Register 7 that stores data to be programmed."]
    #[inline(always)]
    pub const fn pgm_data7(&self) -> &PGM_DATA7 {
        &self.pgm_data7
    }
    #[doc = "0x20 - Register 0 that stores the RS code to be programmed."]
    #[inline(always)]
    pub const fn pgm_check_value0(&self) -> &PGM_CHECK_VALUE0 {
        &self.pgm_check_value0
    }
    #[doc = "0x24 - Register 1 that stores the RS code to be programmed."]
    #[inline(always)]
    pub const fn pgm_check_value1(&self) -> &PGM_CHECK_VALUE1 {
        &self.pgm_check_value1
    }
    #[doc = "0x28 - Register 2 that stores the RS code to be programmed."]
    #[inline(always)]
    pub const fn pgm_check_value2(&self) -> &PGM_CHECK_VALUE2 {
        &self.pgm_check_value2
    }
    #[doc = "0x2c - BLOCK0 data register 0."]
    #[inline(always)]
    pub const fn rd_wr_dis(&self) -> &RD_WR_DIS {
        &self.rd_wr_dis
    }
    #[doc = "0x30 - BLOCK0 data register 1."]
    #[inline(always)]
    pub const fn rd_repeat_data0(&self) -> &RD_REPEAT_DATA0 {
        &self.rd_repeat_data0
    }
    #[doc = "0x34 - BLOCK0 data register 2."]
    #[inline(always)]
    pub const fn rd_repeat_data1(&self) -> &RD_REPEAT_DATA1 {
        &self.rd_repeat_data1
    }
    #[doc = "0x38 - BLOCK0 data register 3."]
    #[inline(always)]
    pub const fn rd_repeat_data2(&self) -> &RD_REPEAT_DATA2 {
        &self.rd_repeat_data2
    }
    #[doc = "0x3c - BLOCK0 data register 4."]
    #[inline(always)]
    pub const fn rd_repeat_data3(&self) -> &RD_REPEAT_DATA3 {
        &self.rd_repeat_data3
    }
    #[doc = "0x40 - BLOCK0 data register 5."]
    #[inline(always)]
    pub const fn rd_repeat_data4(&self) -> &RD_REPEAT_DATA4 {
        &self.rd_repeat_data4
    }
    #[doc = "0x44 - BLOCK1 data register $n."]
    #[inline(always)]
    pub const fn rd_mac_spi_sys_0(&self) -> &RD_MAC_SPI_SYS_0 {
        &self.rd_mac_spi_sys_0
    }
    #[doc = "0x48 - BLOCK1 data register $n."]
    #[inline(always)]
    pub const fn rd_mac_spi_sys_1(&self) -> &RD_MAC_SPI_SYS_1 {
        &self.rd_mac_spi_sys_1
    }
    #[doc = "0x4c - BLOCK1 data register $n."]
    #[inline(always)]
    pub const fn rd_mac_spi_sys_2(&self) -> &RD_MAC_SPI_SYS_2 {
        &self.rd_mac_spi_sys_2
    }
    #[doc = "0x50 - BLOCK1 data register $n."]
    #[inline(always)]
    pub const fn rd_mac_spi_sys_3(&self) -> &RD_MAC_SPI_SYS_3 {
        &self.rd_mac_spi_sys_3
    }
    #[doc = "0x54 - BLOCK1 data register $n."]
    #[inline(always)]
    pub const fn rd_mac_spi_sys_4(&self) -> &RD_MAC_SPI_SYS_4 {
        &self.rd_mac_spi_sys_4
    }
    #[doc = "0x58 - BLOCK1 data register $n."]
    #[inline(always)]
    pub const fn rd_mac_spi_sys_5(&self) -> &RD_MAC_SPI_SYS_5 {
        &self.rd_mac_spi_sys_5
    }
    #[doc = "0x5c - Register $n of BLOCK2 (system)."]
    #[inline(always)]
    pub const fn rd_sys_part1_data0(&self) -> &RD_SYS_PART1_DATA0 {
        &self.rd_sys_part1_data0
    }
    #[doc = "0x60 - Register $n of BLOCK2 (system)."]
    #[inline(always)]
    pub const fn rd_sys_part1_data1(&self) -> &RD_SYS_PART1_DATA1 {
        &self.rd_sys_part1_data1
    }
    #[doc = "0x64 - Register $n of BLOCK2 (system)."]
    #[inline(always)]
    pub const fn rd_sys_part1_data2(&self) -> &RD_SYS_PART1_DATA2 {
        &self.rd_sys_part1_data2
    }
    #[doc = "0x68 - Register $n of BLOCK2 (system)."]
    #[inline(always)]
    pub const fn rd_sys_part1_data3(&self) -> &RD_SYS_PART1_DATA3 {
        &self.rd_sys_part1_data3
    }
    #[doc = "0x6c - Register $n of BLOCK2 (system)."]
    #[inline(always)]
    pub const fn rd_sys_part1_data4(&self) -> &RD_SYS_PART1_DATA4 {
        &self.rd_sys_part1_data4
    }
    #[doc = "0x70 - Register $n of BLOCK2 (system)."]
    #[inline(always)]
    pub const fn rd_sys_part1_data5(&self) -> &RD_SYS_PART1_DATA5 {
        &self.rd_sys_part1_data5
    }
    #[doc = "0x74 - Register $n of BLOCK2 (system)."]
    #[inline(always)]
    pub const fn rd_sys_part1_data6(&self) -> &RD_SYS_PART1_DATA6 {
        &self.rd_sys_part1_data6
    }
    #[doc = "0x78 - Register $n of BLOCK2 (system)."]
    #[inline(always)]
    pub const fn rd_sys_part1_data7(&self) -> &RD_SYS_PART1_DATA7 {
        &self.rd_sys_part1_data7
    }
    #[doc = "0x7c - Register $n of BLOCK3 (user)."]
    #[inline(always)]
    pub const fn rd_usr_data0(&self) -> &RD_USR_DATA0 {
        &self.rd_usr_data0
    }
    #[doc = "0x80 - Register $n of BLOCK3 (user)."]
    #[inline(always)]
    pub const fn rd_usr_data1(&self) -> &RD_USR_DATA1 {
        &self.rd_usr_data1
    }
    #[doc = "0x84 - Register $n of BLOCK3 (user)."]
    #[inline(always)]
    pub const fn rd_usr_data2(&self) -> &RD_USR_DATA2 {
        &self.rd_usr_data2
    }
    #[doc = "0x88 - Register $n of BLOCK3 (user)."]
    #[inline(always)]
    pub const fn rd_usr_data3(&self) -> &RD_USR_DATA3 {
        &self.rd_usr_data3
    }
    #[doc = "0x8c - Register $n of BLOCK3 (user)."]
    #[inline(always)]
    pub const fn rd_usr_data4(&self) -> &RD_USR_DATA4 {
        &self.rd_usr_data4
    }
    #[doc = "0x90 - Register $n of BLOCK3 (user)."]
    #[inline(always)]
    pub const fn rd_usr_data5(&self) -> &RD_USR_DATA5 {
        &self.rd_usr_data5
    }
    #[doc = "0x94 - Register $n of BLOCK3 (user)."]
    #[inline(always)]
    pub const fn rd_usr_data6(&self) -> &RD_USR_DATA6 {
        &self.rd_usr_data6
    }
    #[doc = "0x98 - Register $n of BLOCK3 (user)."]
    #[inline(always)]
    pub const fn rd_usr_data7(&self) -> &RD_USR_DATA7 {
        &self.rd_usr_data7
    }
    #[doc = "0x9c - Register $n of BLOCK4 (KEY0)."]
    #[inline(always)]
    pub const fn rd_key0_data0(&self) -> &RD_KEY0_DATA0 {
        &self.rd_key0_data0
    }
    #[doc = "0xa0 - Register $n of BLOCK4 (KEY0)."]
    #[inline(always)]
    pub const fn rd_key0_data1(&self) -> &RD_KEY0_DATA1 {
        &self.rd_key0_data1
    }
    #[doc = "0xa4 - Register $n of BLOCK4 (KEY0)."]
    #[inline(always)]
    pub const fn rd_key0_data2(&self) -> &RD_KEY0_DATA2 {
        &self.rd_key0_data2
    }
    #[doc = "0xa8 - Register $n of BLOCK4 (KEY0)."]
    #[inline(always)]
    pub const fn rd_key0_data3(&self) -> &RD_KEY0_DATA3 {
        &self.rd_key0_data3
    }
    #[doc = "0xac - Register $n of BLOCK4 (KEY0)."]
    #[inline(always)]
    pub const fn rd_key0_data4(&self) -> &RD_KEY0_DATA4 {
        &self.rd_key0_data4
    }
    #[doc = "0xb0 - Register $n of BLOCK4 (KEY0)."]
    #[inline(always)]
    pub const fn rd_key0_data5(&self) -> &RD_KEY0_DATA5 {
        &self.rd_key0_data5
    }
    #[doc = "0xb4 - Register $n of BLOCK4 (KEY0)."]
    #[inline(always)]
    pub const fn rd_key0_data6(&self) -> &RD_KEY0_DATA6 {
        &self.rd_key0_data6
    }
    #[doc = "0xb8 - Register $n of BLOCK4 (KEY0)."]
    #[inline(always)]
    pub const fn rd_key0_data7(&self) -> &RD_KEY0_DATA7 {
        &self.rd_key0_data7
    }
    #[doc = "0xbc - Register $n of BLOCK5 (KEY1)."]
    #[inline(always)]
    pub const fn rd_key1_data0(&self) -> &RD_KEY1_DATA0 {
        &self.rd_key1_data0
    }
    #[doc = "0xc0 - Register $n of BLOCK5 (KEY1)."]
    #[inline(always)]
    pub const fn rd_key1_data1(&self) -> &RD_KEY1_DATA1 {
        &self.rd_key1_data1
    }
    #[doc = "0xc4 - Register $n of BLOCK5 (KEY1)."]
    #[inline(always)]
    pub const fn rd_key1_data2(&self) -> &RD_KEY1_DATA2 {
        &self.rd_key1_data2
    }
    #[doc = "0xc8 - Register $n of BLOCK5 (KEY1)."]
    #[inline(always)]
    pub const fn rd_key1_data3(&self) -> &RD_KEY1_DATA3 {
        &self.rd_key1_data3
    }
    #[doc = "0xcc - Register $n of BLOCK5 (KEY1)."]
    #[inline(always)]
    pub const fn rd_key1_data4(&self) -> &RD_KEY1_DATA4 {
        &self.rd_key1_data4
    }
    #[doc = "0xd0 - Register $n of BLOCK5 (KEY1)."]
    #[inline(always)]
    pub const fn rd_key1_data5(&self) -> &RD_KEY1_DATA5 {
        &self.rd_key1_data5
    }
    #[doc = "0xd4 - Register $n of BLOCK5 (KEY1)."]
    #[inline(always)]
    pub const fn rd_key1_data6(&self) -> &RD_KEY1_DATA6 {
        &self.rd_key1_data6
    }
    #[doc = "0xd8 - Register $n of BLOCK5 (KEY1)."]
    #[inline(always)]
    pub const fn rd_key1_data7(&self) -> &RD_KEY1_DATA7 {
        &self.rd_key1_data7
    }
    #[doc = "0xdc - Register $n of BLOCK6 (KEY2)."]
    #[inline(always)]
    pub const fn rd_key2_data0(&self) -> &RD_KEY2_DATA0 {
        &self.rd_key2_data0
    }
    #[doc = "0xe0 - Register $n of BLOCK6 (KEY2)."]
    #[inline(always)]
    pub const fn rd_key2_data1(&self) -> &RD_KEY2_DATA1 {
        &self.rd_key2_data1
    }
    #[doc = "0xe4 - Register $n of BLOCK6 (KEY2)."]
    #[inline(always)]
    pub const fn rd_key2_data2(&self) -> &RD_KEY2_DATA2 {
        &self.rd_key2_data2
    }
    #[doc = "0xe8 - Register $n of BLOCK6 (KEY2)."]
    #[inline(always)]
    pub const fn rd_key2_data3(&self) -> &RD_KEY2_DATA3 {
        &self.rd_key2_data3
    }
    #[doc = "0xec - Register $n of BLOCK6 (KEY2)."]
    #[inline(always)]
    pub const fn rd_key2_data4(&self) -> &RD_KEY2_DATA4 {
        &self.rd_key2_data4
    }
    #[doc = "0xf0 - Register $n of BLOCK6 (KEY2)."]
    #[inline(always)]
    pub const fn rd_key2_data5(&self) -> &RD_KEY2_DATA5 {
        &self.rd_key2_data5
    }
    #[doc = "0xf4 - Register $n of BLOCK6 (KEY2)."]
    #[inline(always)]
    pub const fn rd_key2_data6(&self) -> &RD_KEY2_DATA6 {
        &self.rd_key2_data6
    }
    #[doc = "0xf8 - Register $n of BLOCK6 (KEY2)."]
    #[inline(always)]
    pub const fn rd_key2_data7(&self) -> &RD_KEY2_DATA7 {
        &self.rd_key2_data7
    }
    #[doc = "0xfc - Register $n of BLOCK7 (KEY3)."]
    #[inline(always)]
    pub const fn rd_key3_data0(&self) -> &RD_KEY3_DATA0 {
        &self.rd_key3_data0
    }
    #[doc = "0x100 - Register $n of BLOCK7 (KEY3)."]
    #[inline(always)]
    pub const fn rd_key3_data1(&self) -> &RD_KEY3_DATA1 {
        &self.rd_key3_data1
    }
    #[doc = "0x104 - Register $n of BLOCK7 (KEY3)."]
    #[inline(always)]
    pub const fn rd_key3_data2(&self) -> &RD_KEY3_DATA2 {
        &self.rd_key3_data2
    }
    #[doc = "0x108 - Register $n of BLOCK7 (KEY3)."]
    #[inline(always)]
    pub const fn rd_key3_data3(&self) -> &RD_KEY3_DATA3 {
        &self.rd_key3_data3
    }
    #[doc = "0x10c - Register $n of BLOCK7 (KEY3)."]
    #[inline(always)]
    pub const fn rd_key3_data4(&self) -> &RD_KEY3_DATA4 {
        &self.rd_key3_data4
    }
    #[doc = "0x110 - Register $n of BLOCK7 (KEY3)."]
    #[inline(always)]
    pub const fn rd_key3_data5(&self) -> &RD_KEY3_DATA5 {
        &self.rd_key3_data5
    }
    #[doc = "0x114 - Register $n of BLOCK7 (KEY3)."]
    #[inline(always)]
    pub const fn rd_key3_data6(&self) -> &RD_KEY3_DATA6 {
        &self.rd_key3_data6
    }
    #[doc = "0x118 - Register $n of BLOCK7 (KEY3)."]
    #[inline(always)]
    pub const fn rd_key3_data7(&self) -> &RD_KEY3_DATA7 {
        &self.rd_key3_data7
    }
    #[doc = "0x11c - Register $n of BLOCK8 (KEY4)."]
    #[inline(always)]
    pub const fn rd_key4_data0(&self) -> &RD_KEY4_DATA0 {
        &self.rd_key4_data0
    }
    #[doc = "0x120 - Register $n of BLOCK8 (KEY4)."]
    #[inline(always)]
    pub const fn rd_key4_data1(&self) -> &RD_KEY4_DATA1 {
        &self.rd_key4_data1
    }
    #[doc = "0x124 - Register $n of BLOCK8 (KEY4)."]
    #[inline(always)]
    pub const fn rd_key4_data2(&self) -> &RD_KEY4_DATA2 {
        &self.rd_key4_data2
    }
    #[doc = "0x128 - Register $n of BLOCK8 (KEY4)."]
    #[inline(always)]
    pub const fn rd_key4_data3(&self) -> &RD_KEY4_DATA3 {
        &self.rd_key4_data3
    }
    #[doc = "0x12c - Register $n of BLOCK8 (KEY4)."]
    #[inline(always)]
    pub const fn rd_key4_data4(&self) -> &RD_KEY4_DATA4 {
        &self.rd_key4_data4
    }
    #[doc = "0x130 - Register $n of BLOCK8 (KEY4)."]
    #[inline(always)]
    pub const fn rd_key4_data5(&self) -> &RD_KEY4_DATA5 {
        &self.rd_key4_data5
    }
    #[doc = "0x134 - Register $n of BLOCK8 (KEY4)."]
    #[inline(always)]
    pub const fn rd_key4_data6(&self) -> &RD_KEY4_DATA6 {
        &self.rd_key4_data6
    }
    #[doc = "0x138 - Register $n of BLOCK8 (KEY4)."]
    #[inline(always)]
    pub const fn rd_key4_data7(&self) -> &RD_KEY4_DATA7 {
        &self.rd_key4_data7
    }
    #[doc = "0x13c - Register $n of BLOCK9 (KEY5)."]
    #[inline(always)]
    pub const fn rd_key5_data0(&self) -> &RD_KEY5_DATA0 {
        &self.rd_key5_data0
    }
    #[doc = "0x140 - Register $n of BLOCK9 (KEY5)."]
    #[inline(always)]
    pub const fn rd_key5_data1(&self) -> &RD_KEY5_DATA1 {
        &self.rd_key5_data1
    }
    #[doc = "0x144 - Register $n of BLOCK9 (KEY5)."]
    #[inline(always)]
    pub const fn rd_key5_data2(&self) -> &RD_KEY5_DATA2 {
        &self.rd_key5_data2
    }
    #[doc = "0x148 - Register $n of BLOCK9 (KEY5)."]
    #[inline(always)]
    pub const fn rd_key5_data3(&self) -> &RD_KEY5_DATA3 {
        &self.rd_key5_data3
    }
    #[doc = "0x14c - Register $n of BLOCK9 (KEY5)."]
    #[inline(always)]
    pub const fn rd_key5_data4(&self) -> &RD_KEY5_DATA4 {
        &self.rd_key5_data4
    }
    #[doc = "0x150 - Register $n of BLOCK9 (KEY5)."]
    #[inline(always)]
    pub const fn rd_key5_data5(&self) -> &RD_KEY5_DATA5 {
        &self.rd_key5_data5
    }
    #[doc = "0x154 - Register $n of BLOCK9 (KEY5)."]
    #[inline(always)]
    pub const fn rd_key5_data6(&self) -> &RD_KEY5_DATA6 {
        &self.rd_key5_data6
    }
    #[doc = "0x158 - Register $n of BLOCK9 (KEY5)."]
    #[inline(always)]
    pub const fn rd_key5_data7(&self) -> &RD_KEY5_DATA7 {
        &self.rd_key5_data7
    }
    #[doc = "0x15c - Register $n of BLOCK10 (system)."]
    #[inline(always)]
    pub const fn rd_sys_part2_data0(&self) -> &RD_SYS_PART2_DATA0 {
        &self.rd_sys_part2_data0
    }
    #[doc = "0x160 - Register $n of BLOCK9 (KEY5)."]
    #[inline(always)]
    pub const fn rd_sys_part2_data1(&self) -> &RD_SYS_PART2_DATA1 {
        &self.rd_sys_part2_data1
    }
    #[doc = "0x164 - Register $n of BLOCK10 (system)."]
    #[inline(always)]
    pub const fn rd_sys_part2_data2(&self) -> &RD_SYS_PART2_DATA2 {
        &self.rd_sys_part2_data2
    }
    #[doc = "0x168 - Register $n of BLOCK10 (system)."]
    #[inline(always)]
    pub const fn rd_sys_part2_data3(&self) -> &RD_SYS_PART2_DATA3 {
        &self.rd_sys_part2_data3
    }
    #[doc = "0x16c - Register $n of BLOCK10 (system)."]
    #[inline(always)]
    pub const fn rd_sys_part2_data4(&self) -> &RD_SYS_PART2_DATA4 {
        &self.rd_sys_part2_data4
    }
    #[doc = "0x170 - Register $n of BLOCK10 (system)."]
    #[inline(always)]
    pub const fn rd_sys_part2_data5(&self) -> &RD_SYS_PART2_DATA5 {
        &self.rd_sys_part2_data5
    }
    #[doc = "0x174 - Register $n of BLOCK10 (system)."]
    #[inline(always)]
    pub const fn rd_sys_part2_data6(&self) -> &RD_SYS_PART2_DATA6 {
        &self.rd_sys_part2_data6
    }
    #[doc = "0x178 - Register $n of BLOCK10 (system)."]
    #[inline(always)]
    pub const fn rd_sys_part2_data7(&self) -> &RD_SYS_PART2_DATA7 {
        &self.rd_sys_part2_data7
    }
    #[doc = "0x17c - Programming error record register 0 of BLOCK0."]
    #[inline(always)]
    pub const fn rd_repeat_err0(&self) -> &RD_REPEAT_ERR0 {
        &self.rd_repeat_err0
    }
    #[doc = "0x180 - Programming error record register 1 of BLOCK0."]
    #[inline(always)]
    pub const fn rd_repeat_err1(&self) -> &RD_REPEAT_ERR1 {
        &self.rd_repeat_err1
    }
    #[doc = "0x184 - Programming error record register 2 of BLOCK0."]
    #[inline(always)]
    pub const fn rd_repeat_err2(&self) -> &RD_REPEAT_ERR2 {
        &self.rd_repeat_err2
    }
    #[doc = "0x188 - Programming error record register 3 of BLOCK0."]
    #[inline(always)]
    pub const fn rd_repeat_err3(&self) -> &RD_REPEAT_ERR3 {
        &self.rd_repeat_err3
    }
    #[doc = "0x190 - Programming error record register 4 of BLOCK0."]
    #[inline(always)]
    pub const fn rd_repeat_err4(&self) -> &RD_REPEAT_ERR4 {
        &self.rd_repeat_err4
    }
    #[doc = "0x1c0 - Programming error record register 0 of BLOCK1-10."]
    #[inline(always)]
    pub const fn rd_rs_err0(&self) -> &RD_RS_ERR0 {
        &self.rd_rs_err0
    }
    #[doc = "0x1c4 - Programming error record register 1 of BLOCK1-10."]
    #[inline(always)]
    pub const fn rd_rs_err1(&self) -> &RD_RS_ERR1 {
        &self.rd_rs_err1
    }
    #[doc = "0x1c8 - eFuse clcok configuration register."]
    #[inline(always)]
    pub const fn clk(&self) -> &CLK {
        &self.clk
    }
    #[doc = "0x1cc - eFuse operation mode configuraiton register"]
    #[inline(always)]
    pub const fn conf(&self) -> &CONF {
        &self.conf
    }
    #[doc = "0x1d0 - eFuse status register."]
    #[inline(always)]
    pub const fn status(&self) -> &STATUS {
        &self.status
    }
    #[doc = "0x1d4 - eFuse command register."]
    #[inline(always)]
    pub const fn cmd(&self) -> &CMD {
        &self.cmd
    }
    #[doc = "0x1d8 - eFuse raw interrupt register."]
    #[inline(always)]
    pub const fn int_raw(&self) -> &INT_RAW {
        &self.int_raw
    }
    #[doc = "0x1dc - eFuse interrupt status register."]
    #[inline(always)]
    pub const fn int_st(&self) -> &INT_ST {
        &self.int_st
    }
    #[doc = "0x1e0 - eFuse interrupt enable register."]
    #[inline(always)]
    pub const fn int_ena(&self) -> &INT_ENA {
        &self.int_ena
    }
    #[doc = "0x1e4 - eFuse interrupt clear register."]
    #[inline(always)]
    pub const fn int_clr(&self) -> &INT_CLR {
        &self.int_clr
    }
    #[doc = "0x1e8 - Controls the eFuse programming voltage."]
    #[inline(always)]
    pub const fn dac_conf(&self) -> &DAC_CONF {
        &self.dac_conf
    }
    #[doc = "0x1ec - Configures read timing parameters."]
    #[inline(always)]
    pub const fn rd_tim_conf(&self) -> &RD_TIM_CONF {
        &self.rd_tim_conf
    }
    #[doc = "0x1f0 - Configurarion register 1 of eFuse programming timing parameters."]
    #[inline(always)]
    pub const fn wr_tim_conf1(&self) -> &WR_TIM_CONF1 {
        &self.wr_tim_conf1
    }
    #[doc = "0x1f4 - Configurarion register 2 of eFuse programming timing parameters."]
    #[inline(always)]
    pub const fn wr_tim_conf2(&self) -> &WR_TIM_CONF2 {
        &self.wr_tim_conf2
    }
    #[doc = "0x1f8 - Configurarion register0 of eFuse programming time parameters and rs bypass operation."]
    #[inline(always)]
    pub const fn wr_tim_conf0_rs_bypass(&self) -> &WR_TIM_CONF0_RS_BYPASS {
        &self.wr_tim_conf0_rs_bypass
    }
    #[doc = "0x1fc - eFuse version register."]
    #[inline(always)]
    pub const fn date(&self) -> &DATE {
        &self.date
    }
}
#[doc = "PGM_DATA0 (rw) register accessor: Register 0 that stores data to be programmed.\n\nYou can [`read`](crate::Reg::read) this register and get [`pgm_data0::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`pgm_data0::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@pgm_data0`] module"]
pub type PGM_DATA0 = crate::Reg<pgm_data0::PGM_DATA0_SPEC>;
#[doc = "Register 0 that stores data to be programmed."]
pub mod pgm_data0;
#[doc = "PGM_DATA1 (rw) register accessor: Register 1 that stores data to be programmed.\n\nYou can [`read`](crate::Reg::read) this register and get [`pgm_data1::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`pgm_data1::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@pgm_data1`] module"]
pub type PGM_DATA1 = crate::Reg<pgm_data1::PGM_DATA1_SPEC>;
#[doc = "Register 1 that stores data to be programmed."]
pub mod pgm_data1;
#[doc = "PGM_DATA2 (rw) register accessor: Register 2 that stores data to be programmed.\n\nYou can [`read`](crate::Reg::read) this register and get [`pgm_data2::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`pgm_data2::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@pgm_data2`] module"]
pub type PGM_DATA2 = crate::Reg<pgm_data2::PGM_DATA2_SPEC>;
#[doc = "Register 2 that stores data to be programmed."]
pub mod pgm_data2;
#[doc = "PGM_DATA3 (rw) register accessor: Register 3 that stores data to be programmed.\n\nYou can [`read`](crate::Reg::read) this register and get [`pgm_data3::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`pgm_data3::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@pgm_data3`] module"]
pub type PGM_DATA3 = crate::Reg<pgm_data3::PGM_DATA3_SPEC>;
#[doc = "Register 3 that stores data to be programmed."]
pub mod pgm_data3;
#[doc = "PGM_DATA4 (rw) register accessor: Register 4 that stores data to be programmed.\n\nYou can [`read`](crate::Reg::read) this register and get [`pgm_data4::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`pgm_data4::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@pgm_data4`] module"]
pub type PGM_DATA4 = crate::Reg<pgm_data4::PGM_DATA4_SPEC>;
#[doc = "Register 4 that stores data to be programmed."]
pub mod pgm_data4;
#[doc = "PGM_DATA5 (rw) register accessor: Register 5 that stores data to be programmed.\n\nYou can [`read`](crate::Reg::read) this register and get [`pgm_data5::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`pgm_data5::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@pgm_data5`] module"]
pub type PGM_DATA5 = crate::Reg<pgm_data5::PGM_DATA5_SPEC>;
#[doc = "Register 5 that stores data to be programmed."]
pub mod pgm_data5;
#[doc = "PGM_DATA6 (rw) register accessor: Register 6 that stores data to be programmed.\n\nYou can [`read`](crate::Reg::read) this register and get [`pgm_data6::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`pgm_data6::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@pgm_data6`] module"]
pub type PGM_DATA6 = crate::Reg<pgm_data6::PGM_DATA6_SPEC>;
#[doc = "Register 6 that stores data to be programmed."]
pub mod pgm_data6;
#[doc = "PGM_DATA7 (rw) register accessor: Register 7 that stores data to be programmed.\n\nYou can [`read`](crate::Reg::read) this register and get [`pgm_data7::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`pgm_data7::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@pgm_data7`] module"]
pub type PGM_DATA7 = crate::Reg<pgm_data7::PGM_DATA7_SPEC>;
#[doc = "Register 7 that stores data to be programmed."]
pub mod pgm_data7;
#[doc = "PGM_CHECK_VALUE0 (rw) register accessor: Register 0 that stores the RS code to be programmed.\n\nYou can [`read`](crate::Reg::read) this register and get [`pgm_check_value0::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`pgm_check_value0::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@pgm_check_value0`] module"]
pub type PGM_CHECK_VALUE0 = crate::Reg<pgm_check_value0::PGM_CHECK_VALUE0_SPEC>;
#[doc = "Register 0 that stores the RS code to be programmed."]
pub mod pgm_check_value0;
#[doc = "PGM_CHECK_VALUE1 (rw) register accessor: Register 1 that stores the RS code to be programmed.\n\nYou can [`read`](crate::Reg::read) this register and get [`pgm_check_value1::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`pgm_check_value1::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@pgm_check_value1`] module"]
pub type PGM_CHECK_VALUE1 = crate::Reg<pgm_check_value1::PGM_CHECK_VALUE1_SPEC>;
#[doc = "Register 1 that stores the RS code to be programmed."]
pub mod pgm_check_value1;
#[doc = "PGM_CHECK_VALUE2 (rw) register accessor: Register 2 that stores the RS code to be programmed.\n\nYou can [`read`](crate::Reg::read) this register and get [`pgm_check_value2::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`pgm_check_value2::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@pgm_check_value2`] module"]
pub type PGM_CHECK_VALUE2 = crate::Reg<pgm_check_value2::PGM_CHECK_VALUE2_SPEC>;
#[doc = "Register 2 that stores the RS code to be programmed."]
pub mod pgm_check_value2;
#[doc = "RD_WR_DIS (r) register accessor: BLOCK0 data register 0.\n\nYou can [`read`](crate::Reg::read) this register and get [`rd_wr_dis::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@rd_wr_dis`] module"]
pub type RD_WR_DIS = crate::Reg<rd_wr_dis::RD_WR_DIS_SPEC>;
#[doc = "BLOCK0 data register 0."]
pub mod rd_wr_dis;
#[doc = "RD_REPEAT_DATA0 (r) register accessor: BLOCK0 data register 1.\n\nYou can [`read`](crate::Reg::read) this register and get [`rd_repeat_data0::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@rd_repeat_data0`] module"]
pub type RD_REPEAT_DATA0 = crate::Reg<rd_repeat_data0::RD_REPEAT_DATA0_SPEC>;
#[doc = "BLOCK0 data register 1."]
pub mod rd_repeat_data0;
#[doc = "RD_REPEAT_DATA1 (r) register accessor: BLOCK0 data register 2.\n\nYou can [`read`](crate::Reg::read) this register and get [`rd_repeat_data1::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@rd_repeat_data1`] module"]
pub type RD_REPEAT_DATA1 = crate::Reg<rd_repeat_data1::RD_REPEAT_DATA1_SPEC>;
#[doc = "BLOCK0 data register 2."]
pub mod rd_repeat_data1;
#[doc = "RD_REPEAT_DATA2 (r) register accessor: BLOCK0 data register 3.\n\nYou can [`read`](crate::Reg::read) this register and get [`rd_repeat_data2::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@rd_repeat_data2`] module"]
pub type RD_REPEAT_DATA2 = crate::Reg<rd_repeat_data2::RD_REPEAT_DATA2_SPEC>;
#[doc = "BLOCK0 data register 3."]
pub mod rd_repeat_data2;
#[doc = "RD_REPEAT_DATA3 (r) register accessor: BLOCK0 data register 4.\n\nYou can [`read`](crate::Reg::read) this register and get [`rd_repeat_data3::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@rd_repeat_data3`] module"]
pub type RD_REPEAT_DATA3 = crate::Reg<rd_repeat_data3::RD_REPEAT_DATA3_SPEC>;
#[doc = "BLOCK0 data register 4."]
pub mod rd_repeat_data3;
#[doc = "RD_REPEAT_DATA4 (r) register accessor: BLOCK0 data register 5.\n\nYou can [`read`](crate::Reg::read) this register and get [`rd_repeat_data4::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@rd_repeat_data4`] module"]
pub type RD_REPEAT_DATA4 = crate::Reg<rd_repeat_data4::RD_REPEAT_DATA4_SPEC>;
#[doc = "BLOCK0 data register 5."]
pub mod rd_repeat_data4;
#[doc = "RD_MAC_SPI_SYS_0 (r) register accessor: BLOCK1 data register $n.\n\nYou can [`read`](crate::Reg::read) this register and get [`rd_mac_spi_sys_0::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@rd_mac_spi_sys_0`] module"]
pub type RD_MAC_SPI_SYS_0 = crate::Reg<rd_mac_spi_sys_0::RD_MAC_SPI_SYS_0_SPEC>;
#[doc = "BLOCK1 data register $n."]
pub mod rd_mac_spi_sys_0;
#[doc = "RD_MAC_SPI_SYS_1 (r) register accessor: BLOCK1 data register $n.\n\nYou can [`read`](crate::Reg::read) this register and get [`rd_mac_spi_sys_1::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@rd_mac_spi_sys_1`] module"]
pub type RD_MAC_SPI_SYS_1 = crate::Reg<rd_mac_spi_sys_1::RD_MAC_SPI_SYS_1_SPEC>;
#[doc = "BLOCK1 data register $n."]
pub mod rd_mac_spi_sys_1;
#[doc = "RD_MAC_SPI_SYS_2 (r) register accessor: BLOCK1 data register $n.\n\nYou can [`read`](crate::Reg::read) this register and get [`rd_mac_spi_sys_2::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@rd_mac_spi_sys_2`] module"]
pub type RD_MAC_SPI_SYS_2 = crate::Reg<rd_mac_spi_sys_2::RD_MAC_SPI_SYS_2_SPEC>;
#[doc = "BLOCK1 data register $n."]
pub mod rd_mac_spi_sys_2;
#[doc = "RD_MAC_SPI_SYS_3 (r) register accessor: BLOCK1 data register $n.\n\nYou can [`read`](crate::Reg::read) this register and get [`rd_mac_spi_sys_3::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@rd_mac_spi_sys_3`] module"]
pub type RD_MAC_SPI_SYS_3 = crate::Reg<rd_mac_spi_sys_3::RD_MAC_SPI_SYS_3_SPEC>;
#[doc = "BLOCK1 data register $n."]
pub mod rd_mac_spi_sys_3;
#[doc = "RD_MAC_SPI_SYS_4 (r) register accessor: BLOCK1 data register $n.\n\nYou can [`read`](crate::Reg::read) this register and get [`rd_mac_spi_sys_4::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@rd_mac_spi_sys_4`] module"]
pub type RD_MAC_SPI_SYS_4 = crate::Reg<rd_mac_spi_sys_4::RD_MAC_SPI_SYS_4_SPEC>;
#[doc = "BLOCK1 data register $n."]
pub mod rd_mac_spi_sys_4;
#[doc = "RD_MAC_SPI_SYS_5 (r) register accessor: BLOCK1 data register $n.\n\nYou can [`read`](crate::Reg::read) this register and get [`rd_mac_spi_sys_5::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@rd_mac_spi_sys_5`] module"]
pub type RD_MAC_SPI_SYS_5 = crate::Reg<rd_mac_spi_sys_5::RD_MAC_SPI_SYS_5_SPEC>;
#[doc = "BLOCK1 data register $n."]
pub mod rd_mac_spi_sys_5;
#[doc = "RD_SYS_PART1_DATA0 (r) register accessor: Register $n of BLOCK2 (system).\n\nYou can [`read`](crate::Reg::read) this register and get [`rd_sys_part1_data0::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@rd_sys_part1_data0`] module"]
pub type RD_SYS_PART1_DATA0 = crate::Reg<rd_sys_part1_data0::RD_SYS_PART1_DATA0_SPEC>;
#[doc = "Register $n of BLOCK2 (system)."]
pub mod rd_sys_part1_data0;
#[doc = "RD_SYS_PART1_DATA1 (r) register accessor: Register $n of BLOCK2 (system).\n\nYou can [`read`](crate::Reg::read) this register and get [`rd_sys_part1_data1::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@rd_sys_part1_data1`] module"]
pub type RD_SYS_PART1_DATA1 = crate::Reg<rd_sys_part1_data1::RD_SYS_PART1_DATA1_SPEC>;
#[doc = "Register $n of BLOCK2 (system)."]
pub mod rd_sys_part1_data1;
#[doc = "RD_SYS_PART1_DATA2 (r) register accessor: Register $n of BLOCK2 (system).\n\nYou can [`read`](crate::Reg::read) this register and get [`rd_sys_part1_data2::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@rd_sys_part1_data2`] module"]
pub type RD_SYS_PART1_DATA2 = crate::Reg<rd_sys_part1_data2::RD_SYS_PART1_DATA2_SPEC>;
#[doc = "Register $n of BLOCK2 (system)."]
pub mod rd_sys_part1_data2;
#[doc = "RD_SYS_PART1_DATA3 (r) register accessor: Register $n of BLOCK2 (system).\n\nYou can [`read`](crate::Reg::read) this register and get [`rd_sys_part1_data3::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@rd_sys_part1_data3`] module"]
pub type RD_SYS_PART1_DATA3 = crate::Reg<rd_sys_part1_data3::RD_SYS_PART1_DATA3_SPEC>;
#[doc = "Register $n of BLOCK2 (system)."]
pub mod rd_sys_part1_data3;
#[doc = "RD_SYS_PART1_DATA4 (r) register accessor: Register $n of BLOCK2 (system).\n\nYou can [`read`](crate::Reg::read) this register and get [`rd_sys_part1_data4::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@rd_sys_part1_data4`] module"]
pub type RD_SYS_PART1_DATA4 = crate::Reg<rd_sys_part1_data4::RD_SYS_PART1_DATA4_SPEC>;
#[doc = "Register $n of BLOCK2 (system)."]
pub mod rd_sys_part1_data4;
#[doc = "RD_SYS_PART1_DATA5 (r) register accessor: Register $n of BLOCK2 (system).\n\nYou can [`read`](crate::Reg::read) this register and get [`rd_sys_part1_data5::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@rd_sys_part1_data5`] module"]
pub type RD_SYS_PART1_DATA5 = crate::Reg<rd_sys_part1_data5::RD_SYS_PART1_DATA5_SPEC>;
#[doc = "Register $n of BLOCK2 (system)."]
pub mod rd_sys_part1_data5;
#[doc = "RD_SYS_PART1_DATA6 (r) register accessor: Register $n of BLOCK2 (system).\n\nYou can [`read`](crate::Reg::read) this register and get [`rd_sys_part1_data6::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@rd_sys_part1_data6`] module"]
pub type RD_SYS_PART1_DATA6 = crate::Reg<rd_sys_part1_data6::RD_SYS_PART1_DATA6_SPEC>;
#[doc = "Register $n of BLOCK2 (system)."]
pub mod rd_sys_part1_data6;
#[doc = "RD_SYS_PART1_DATA7 (r) register accessor: Register $n of BLOCK2 (system).\n\nYou can [`read`](crate::Reg::read) this register and get [`rd_sys_part1_data7::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@rd_sys_part1_data7`] module"]
pub type RD_SYS_PART1_DATA7 = crate::Reg<rd_sys_part1_data7::RD_SYS_PART1_DATA7_SPEC>;
#[doc = "Register $n of BLOCK2 (system)."]
pub mod rd_sys_part1_data7;
#[doc = "RD_USR_DATA0 (r) register accessor: Register $n of BLOCK3 (user).\n\nYou can [`read`](crate::Reg::read) this register and get [`rd_usr_data0::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@rd_usr_data0`] module"]
pub type RD_USR_DATA0 = crate::Reg<rd_usr_data0::RD_USR_DATA0_SPEC>;
#[doc = "Register $n of BLOCK3 (user)."]
pub mod rd_usr_data0;
#[doc = "RD_USR_DATA1 (r) register accessor: Register $n of BLOCK3 (user).\n\nYou can [`read`](crate::Reg::read) this register and get [`rd_usr_data1::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@rd_usr_data1`] module"]
pub type RD_USR_DATA1 = crate::Reg<rd_usr_data1::RD_USR_DATA1_SPEC>;
#[doc = "Register $n of BLOCK3 (user)."]
pub mod rd_usr_data1;
#[doc = "RD_USR_DATA2 (r) register accessor: Register $n of BLOCK3 (user).\n\nYou can [`read`](crate::Reg::read) this register and get [`rd_usr_data2::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@rd_usr_data2`] module"]
pub type RD_USR_DATA2 = crate::Reg<rd_usr_data2::RD_USR_DATA2_SPEC>;
#[doc = "Register $n of BLOCK3 (user)."]
pub mod rd_usr_data2;
#[doc = "RD_USR_DATA3 (r) register accessor: Register $n of BLOCK3 (user).\n\nYou can [`read`](crate::Reg::read) this register and get [`rd_usr_data3::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@rd_usr_data3`] module"]
pub type RD_USR_DATA3 = crate::Reg<rd_usr_data3::RD_USR_DATA3_SPEC>;
#[doc = "Register $n of BLOCK3 (user)."]
pub mod rd_usr_data3;
#[doc = "RD_USR_DATA4 (r) register accessor: Register $n of BLOCK3 (user).\n\nYou can [`read`](crate::Reg::read) this register and get [`rd_usr_data4::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@rd_usr_data4`] module"]
pub type RD_USR_DATA4 = crate::Reg<rd_usr_data4::RD_USR_DATA4_SPEC>;
#[doc = "Register $n of BLOCK3 (user)."]
pub mod rd_usr_data4;
#[doc = "RD_USR_DATA5 (r) register accessor: Register $n of BLOCK3 (user).\n\nYou can [`read`](crate::Reg::read) this register and get [`rd_usr_data5::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@rd_usr_data5`] module"]
pub type RD_USR_DATA5 = crate::Reg<rd_usr_data5::RD_USR_DATA5_SPEC>;
#[doc = "Register $n of BLOCK3 (user)."]
pub mod rd_usr_data5;
#[doc = "RD_USR_DATA6 (r) register accessor: Register $n of BLOCK3 (user).\n\nYou can [`read`](crate::Reg::read) this register and get [`rd_usr_data6::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@rd_usr_data6`] module"]
pub type RD_USR_DATA6 = crate::Reg<rd_usr_data6::RD_USR_DATA6_SPEC>;
#[doc = "Register $n of BLOCK3 (user)."]
pub mod rd_usr_data6;
#[doc = "RD_USR_DATA7 (r) register accessor: Register $n of BLOCK3 (user).\n\nYou can [`read`](crate::Reg::read) this register and get [`rd_usr_data7::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@rd_usr_data7`] module"]
pub type RD_USR_DATA7 = crate::Reg<rd_usr_data7::RD_USR_DATA7_SPEC>;
#[doc = "Register $n of BLOCK3 (user)."]
pub mod rd_usr_data7;
#[doc = "RD_KEY0_DATA0 (r) register accessor: Register $n of BLOCK4 (KEY0).\n\nYou can [`read`](crate::Reg::read) this register and get [`rd_key0_data0::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@rd_key0_data0`] module"]
pub type RD_KEY0_DATA0 = crate::Reg<rd_key0_data0::RD_KEY0_DATA0_SPEC>;
#[doc = "Register $n of BLOCK4 (KEY0)."]
pub mod rd_key0_data0;
#[doc = "RD_KEY0_DATA1 (r) register accessor: Register $n of BLOCK4 (KEY0).\n\nYou can [`read`](crate::Reg::read) this register and get [`rd_key0_data1::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@rd_key0_data1`] module"]
pub type RD_KEY0_DATA1 = crate::Reg<rd_key0_data1::RD_KEY0_DATA1_SPEC>;
#[doc = "Register $n of BLOCK4 (KEY0)."]
pub mod rd_key0_data1;
#[doc = "RD_KEY0_DATA2 (r) register accessor: Register $n of BLOCK4 (KEY0).\n\nYou can [`read`](crate::Reg::read) this register and get [`rd_key0_data2::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@rd_key0_data2`] module"]
pub type RD_KEY0_DATA2 = crate::Reg<rd_key0_data2::RD_KEY0_DATA2_SPEC>;
#[doc = "Register $n of BLOCK4 (KEY0)."]
pub mod rd_key0_data2;
#[doc = "RD_KEY0_DATA3 (r) register accessor: Register $n of BLOCK4 (KEY0).\n\nYou can [`read`](crate::Reg::read) this register and get [`rd_key0_data3::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@rd_key0_data3`] module"]
pub type RD_KEY0_DATA3 = crate::Reg<rd_key0_data3::RD_KEY0_DATA3_SPEC>;
#[doc = "Register $n of BLOCK4 (KEY0)."]
pub mod rd_key0_data3;
#[doc = "RD_KEY0_DATA4 (r) register accessor: Register $n of BLOCK4 (KEY0).\n\nYou can [`read`](crate::Reg::read) this register and get [`rd_key0_data4::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@rd_key0_data4`] module"]
pub type RD_KEY0_DATA4 = crate::Reg<rd_key0_data4::RD_KEY0_DATA4_SPEC>;
#[doc = "Register $n of BLOCK4 (KEY0)."]
pub mod rd_key0_data4;
#[doc = "RD_KEY0_DATA5 (r) register accessor: Register $n of BLOCK4 (KEY0).\n\nYou can [`read`](crate::Reg::read) this register and get [`rd_key0_data5::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@rd_key0_data5`] module"]
pub type RD_KEY0_DATA5 = crate::Reg<rd_key0_data5::RD_KEY0_DATA5_SPEC>;
#[doc = "Register $n of BLOCK4 (KEY0)."]
pub mod rd_key0_data5;
#[doc = "RD_KEY0_DATA6 (r) register accessor: Register $n of BLOCK4 (KEY0).\n\nYou can [`read`](crate::Reg::read) this register and get [`rd_key0_data6::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@rd_key0_data6`] module"]
pub type RD_KEY0_DATA6 = crate::Reg<rd_key0_data6::RD_KEY0_DATA6_SPEC>;
#[doc = "Register $n of BLOCK4 (KEY0)."]
pub mod rd_key0_data6;
#[doc = "RD_KEY0_DATA7 (r) register accessor: Register $n of BLOCK4 (KEY0).\n\nYou can [`read`](crate::Reg::read) this register and get [`rd_key0_data7::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@rd_key0_data7`] module"]
pub type RD_KEY0_DATA7 = crate::Reg<rd_key0_data7::RD_KEY0_DATA7_SPEC>;
#[doc = "Register $n of BLOCK4 (KEY0)."]
pub mod rd_key0_data7;
#[doc = "RD_KEY1_DATA0 (r) register accessor: Register $n of BLOCK5 (KEY1).\n\nYou can [`read`](crate::Reg::read) this register and get [`rd_key1_data0::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@rd_key1_data0`] module"]
pub type RD_KEY1_DATA0 = crate::Reg<rd_key1_data0::RD_KEY1_DATA0_SPEC>;
#[doc = "Register $n of BLOCK5 (KEY1)."]
pub mod rd_key1_data0;
#[doc = "RD_KEY1_DATA1 (r) register accessor: Register $n of BLOCK5 (KEY1).\n\nYou can [`read`](crate::Reg::read) this register and get [`rd_key1_data1::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@rd_key1_data1`] module"]
pub type RD_KEY1_DATA1 = crate::Reg<rd_key1_data1::RD_KEY1_DATA1_SPEC>;
#[doc = "Register $n of BLOCK5 (KEY1)."]
pub mod rd_key1_data1;
#[doc = "RD_KEY1_DATA2 (r) register accessor: Register $n of BLOCK5 (KEY1).\n\nYou can [`read`](crate::Reg::read) this register and get [`rd_key1_data2::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@rd_key1_data2`] module"]
pub type RD_KEY1_DATA2 = crate::Reg<rd_key1_data2::RD_KEY1_DATA2_SPEC>;
#[doc = "Register $n of BLOCK5 (KEY1)."]
pub mod rd_key1_data2;
#[doc = "RD_KEY1_DATA3 (r) register accessor: Register $n of BLOCK5 (KEY1).\n\nYou can [`read`](crate::Reg::read) this register and get [`rd_key1_data3::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@rd_key1_data3`] module"]
pub type RD_KEY1_DATA3 = crate::Reg<rd_key1_data3::RD_KEY1_DATA3_SPEC>;
#[doc = "Register $n of BLOCK5 (KEY1)."]
pub mod rd_key1_data3;
#[doc = "RD_KEY1_DATA4 (r) register accessor: Register $n of BLOCK5 (KEY1).\n\nYou can [`read`](crate::Reg::read) this register and get [`rd_key1_data4::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@rd_key1_data4`] module"]
pub type RD_KEY1_DATA4 = crate::Reg<rd_key1_data4::RD_KEY1_DATA4_SPEC>;
#[doc = "Register $n of BLOCK5 (KEY1)."]
pub mod rd_key1_data4;
#[doc = "RD_KEY1_DATA5 (r) register accessor: Register $n of BLOCK5 (KEY1).\n\nYou can [`read`](crate::Reg::read) this register and get [`rd_key1_data5::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@rd_key1_data5`] module"]
pub type RD_KEY1_DATA5 = crate::Reg<rd_key1_data5::RD_KEY1_DATA5_SPEC>;
#[doc = "Register $n of BLOCK5 (KEY1)."]
pub mod rd_key1_data5;
#[doc = "RD_KEY1_DATA6 (r) register accessor: Register $n of BLOCK5 (KEY1).\n\nYou can [`read`](crate::Reg::read) this register and get [`rd_key1_data6::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@rd_key1_data6`] module"]
pub type RD_KEY1_DATA6 = crate::Reg<rd_key1_data6::RD_KEY1_DATA6_SPEC>;
#[doc = "Register $n of BLOCK5 (KEY1)."]
pub mod rd_key1_data6;
#[doc = "RD_KEY1_DATA7 (r) register accessor: Register $n of BLOCK5 (KEY1).\n\nYou can [`read`](crate::Reg::read) this register and get [`rd_key1_data7::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@rd_key1_data7`] module"]
pub type RD_KEY1_DATA7 = crate::Reg<rd_key1_data7::RD_KEY1_DATA7_SPEC>;
#[doc = "Register $n of BLOCK5 (KEY1)."]
pub mod rd_key1_data7;
#[doc = "RD_KEY2_DATA0 (r) register accessor: Register $n of BLOCK6 (KEY2).\n\nYou can [`read`](crate::Reg::read) this register and get [`rd_key2_data0::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@rd_key2_data0`] module"]
pub type RD_KEY2_DATA0 = crate::Reg<rd_key2_data0::RD_KEY2_DATA0_SPEC>;
#[doc = "Register $n of BLOCK6 (KEY2)."]
pub mod rd_key2_data0;
#[doc = "RD_KEY2_DATA1 (r) register accessor: Register $n of BLOCK6 (KEY2).\n\nYou can [`read`](crate::Reg::read) this register and get [`rd_key2_data1::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@rd_key2_data1`] module"]
pub type RD_KEY2_DATA1 = crate::Reg<rd_key2_data1::RD_KEY2_DATA1_SPEC>;
#[doc = "Register $n of BLOCK6 (KEY2)."]
pub mod rd_key2_data1;
#[doc = "RD_KEY2_DATA2 (r) register accessor: Register $n of BLOCK6 (KEY2).\n\nYou can [`read`](crate::Reg::read) this register and get [`rd_key2_data2::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@rd_key2_data2`] module"]
pub type RD_KEY2_DATA2 = crate::Reg<rd_key2_data2::RD_KEY2_DATA2_SPEC>;
#[doc = "Register $n of BLOCK6 (KEY2)."]
pub mod rd_key2_data2;
#[doc = "RD_KEY2_DATA3 (r) register accessor: Register $n of BLOCK6 (KEY2).\n\nYou can [`read`](crate::Reg::read) this register and get [`rd_key2_data3::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@rd_key2_data3`] module"]
pub type RD_KEY2_DATA3 = crate::Reg<rd_key2_data3::RD_KEY2_DATA3_SPEC>;
#[doc = "Register $n of BLOCK6 (KEY2)."]
pub mod rd_key2_data3;
#[doc = "RD_KEY2_DATA4 (r) register accessor: Register $n of BLOCK6 (KEY2).\n\nYou can [`read`](crate::Reg::read) this register and get [`rd_key2_data4::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@rd_key2_data4`] module"]
pub type RD_KEY2_DATA4 = crate::Reg<rd_key2_data4::RD_KEY2_DATA4_SPEC>;
#[doc = "Register $n of BLOCK6 (KEY2)."]
pub mod rd_key2_data4;
#[doc = "RD_KEY2_DATA5 (r) register accessor: Register $n of BLOCK6 (KEY2).\n\nYou can [`read`](crate::Reg::read) this register and get [`rd_key2_data5::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@rd_key2_data5`] module"]
pub type RD_KEY2_DATA5 = crate::Reg<rd_key2_data5::RD_KEY2_DATA5_SPEC>;
#[doc = "Register $n of BLOCK6 (KEY2)."]
pub mod rd_key2_data5;
#[doc = "RD_KEY2_DATA6 (r) register accessor: Register $n of BLOCK6 (KEY2).\n\nYou can [`read`](crate::Reg::read) this register and get [`rd_key2_data6::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@rd_key2_data6`] module"]
pub type RD_KEY2_DATA6 = crate::Reg<rd_key2_data6::RD_KEY2_DATA6_SPEC>;
#[doc = "Register $n of BLOCK6 (KEY2)."]
pub mod rd_key2_data6;
#[doc = "RD_KEY2_DATA7 (r) register accessor: Register $n of BLOCK6 (KEY2).\n\nYou can [`read`](crate::Reg::read) this register and get [`rd_key2_data7::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@rd_key2_data7`] module"]
pub type RD_KEY2_DATA7 = crate::Reg<rd_key2_data7::RD_KEY2_DATA7_SPEC>;
#[doc = "Register $n of BLOCK6 (KEY2)."]
pub mod rd_key2_data7;
#[doc = "RD_KEY3_DATA0 (r) register accessor: Register $n of BLOCK7 (KEY3).\n\nYou can [`read`](crate::Reg::read) this register and get [`rd_key3_data0::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@rd_key3_data0`] module"]
pub type RD_KEY3_DATA0 = crate::Reg<rd_key3_data0::RD_KEY3_DATA0_SPEC>;
#[doc = "Register $n of BLOCK7 (KEY3)."]
pub mod rd_key3_data0;
#[doc = "RD_KEY3_DATA1 (r) register accessor: Register $n of BLOCK7 (KEY3).\n\nYou can [`read`](crate::Reg::read) this register and get [`rd_key3_data1::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@rd_key3_data1`] module"]
pub type RD_KEY3_DATA1 = crate::Reg<rd_key3_data1::RD_KEY3_DATA1_SPEC>;
#[doc = "Register $n of BLOCK7 (KEY3)."]
pub mod rd_key3_data1;
#[doc = "RD_KEY3_DATA2 (r) register accessor: Register $n of BLOCK7 (KEY3).\n\nYou can [`read`](crate::Reg::read) this register and get [`rd_key3_data2::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@rd_key3_data2`] module"]
pub type RD_KEY3_DATA2 = crate::Reg<rd_key3_data2::RD_KEY3_DATA2_SPEC>;
#[doc = "Register $n of BLOCK7 (KEY3)."]
pub mod rd_key3_data2;
#[doc = "RD_KEY3_DATA3 (r) register accessor: Register $n of BLOCK7 (KEY3).\n\nYou can [`read`](crate::Reg::read) this register and get [`rd_key3_data3::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@rd_key3_data3`] module"]
pub type RD_KEY3_DATA3 = crate::Reg<rd_key3_data3::RD_KEY3_DATA3_SPEC>;
#[doc = "Register $n of BLOCK7 (KEY3)."]
pub mod rd_key3_data3;
#[doc = "RD_KEY3_DATA4 (r) register accessor: Register $n of BLOCK7 (KEY3).\n\nYou can [`read`](crate::Reg::read) this register and get [`rd_key3_data4::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@rd_key3_data4`] module"]
pub type RD_KEY3_DATA4 = crate::Reg<rd_key3_data4::RD_KEY3_DATA4_SPEC>;
#[doc = "Register $n of BLOCK7 (KEY3)."]
pub mod rd_key3_data4;
#[doc = "RD_KEY3_DATA5 (r) register accessor: Register $n of BLOCK7 (KEY3).\n\nYou can [`read`](crate::Reg::read) this register and get [`rd_key3_data5::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@rd_key3_data5`] module"]
pub type RD_KEY3_DATA5 = crate::Reg<rd_key3_data5::RD_KEY3_DATA5_SPEC>;
#[doc = "Register $n of BLOCK7 (KEY3)."]
pub mod rd_key3_data5;
#[doc = "RD_KEY3_DATA6 (r) register accessor: Register $n of BLOCK7 (KEY3).\n\nYou can [`read`](crate::Reg::read) this register and get [`rd_key3_data6::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@rd_key3_data6`] module"]
pub type RD_KEY3_DATA6 = crate::Reg<rd_key3_data6::RD_KEY3_DATA6_SPEC>;
#[doc = "Register $n of BLOCK7 (KEY3)."]
pub mod rd_key3_data6;
#[doc = "RD_KEY3_DATA7 (r) register accessor: Register $n of BLOCK7 (KEY3).\n\nYou can [`read`](crate::Reg::read) this register and get [`rd_key3_data7::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@rd_key3_data7`] module"]
pub type RD_KEY3_DATA7 = crate::Reg<rd_key3_data7::RD_KEY3_DATA7_SPEC>;
#[doc = "Register $n of BLOCK7 (KEY3)."]
pub mod rd_key3_data7;
#[doc = "RD_KEY4_DATA0 (r) register accessor: Register $n of BLOCK8 (KEY4).\n\nYou can [`read`](crate::Reg::read) this register and get [`rd_key4_data0::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@rd_key4_data0`] module"]
pub type RD_KEY4_DATA0 = crate::Reg<rd_key4_data0::RD_KEY4_DATA0_SPEC>;
#[doc = "Register $n of BLOCK8 (KEY4)."]
pub mod rd_key4_data0;
#[doc = "RD_KEY4_DATA1 (r) register accessor: Register $n of BLOCK8 (KEY4).\n\nYou can [`read`](crate::Reg::read) this register and get [`rd_key4_data1::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@rd_key4_data1`] module"]
pub type RD_KEY4_DATA1 = crate::Reg<rd_key4_data1::RD_KEY4_DATA1_SPEC>;
#[doc = "Register $n of BLOCK8 (KEY4)."]
pub mod rd_key4_data1;
#[doc = "RD_KEY4_DATA2 (r) register accessor: Register $n of BLOCK8 (KEY4).\n\nYou can [`read`](crate::Reg::read) this register and get [`rd_key4_data2::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@rd_key4_data2`] module"]
pub type RD_KEY4_DATA2 = crate::Reg<rd_key4_data2::RD_KEY4_DATA2_SPEC>;
#[doc = "Register $n of BLOCK8 (KEY4)."]
pub mod rd_key4_data2;
#[doc = "RD_KEY4_DATA3 (r) register accessor: Register $n of BLOCK8 (KEY4).\n\nYou can [`read`](crate::Reg::read) this register and get [`rd_key4_data3::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@rd_key4_data3`] module"]
pub type RD_KEY4_DATA3 = crate::Reg<rd_key4_data3::RD_KEY4_DATA3_SPEC>;
#[doc = "Register $n of BLOCK8 (KEY4)."]
pub mod rd_key4_data3;
#[doc = "RD_KEY4_DATA4 (r) register accessor: Register $n of BLOCK8 (KEY4).\n\nYou can [`read`](crate::Reg::read) this register and get [`rd_key4_data4::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@rd_key4_data4`] module"]
pub type RD_KEY4_DATA4 = crate::Reg<rd_key4_data4::RD_KEY4_DATA4_SPEC>;
#[doc = "Register $n of BLOCK8 (KEY4)."]
pub mod rd_key4_data4;
#[doc = "RD_KEY4_DATA5 (r) register accessor: Register $n of BLOCK8 (KEY4).\n\nYou can [`read`](crate::Reg::read) this register and get [`rd_key4_data5::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@rd_key4_data5`] module"]
pub type RD_KEY4_DATA5 = crate::Reg<rd_key4_data5::RD_KEY4_DATA5_SPEC>;
#[doc = "Register $n of BLOCK8 (KEY4)."]
pub mod rd_key4_data5;
#[doc = "RD_KEY4_DATA6 (r) register accessor: Register $n of BLOCK8 (KEY4).\n\nYou can [`read`](crate::Reg::read) this register and get [`rd_key4_data6::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@rd_key4_data6`] module"]
pub type RD_KEY4_DATA6 = crate::Reg<rd_key4_data6::RD_KEY4_DATA6_SPEC>;
#[doc = "Register $n of BLOCK8 (KEY4)."]
pub mod rd_key4_data6;
#[doc = "RD_KEY4_DATA7 (r) register accessor: Register $n of BLOCK8 (KEY4).\n\nYou can [`read`](crate::Reg::read) this register and get [`rd_key4_data7::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@rd_key4_data7`] module"]
pub type RD_KEY4_DATA7 = crate::Reg<rd_key4_data7::RD_KEY4_DATA7_SPEC>;
#[doc = "Register $n of BLOCK8 (KEY4)."]
pub mod rd_key4_data7;
#[doc = "RD_KEY5_DATA0 (r) register accessor: Register $n of BLOCK9 (KEY5).\n\nYou can [`read`](crate::Reg::read) this register and get [`rd_key5_data0::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@rd_key5_data0`] module"]
pub type RD_KEY5_DATA0 = crate::Reg<rd_key5_data0::RD_KEY5_DATA0_SPEC>;
#[doc = "Register $n of BLOCK9 (KEY5)."]
pub mod rd_key5_data0;
#[doc = "RD_KEY5_DATA1 (r) register accessor: Register $n of BLOCK9 (KEY5).\n\nYou can [`read`](crate::Reg::read) this register and get [`rd_key5_data1::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@rd_key5_data1`] module"]
pub type RD_KEY5_DATA1 = crate::Reg<rd_key5_data1::RD_KEY5_DATA1_SPEC>;
#[doc = "Register $n of BLOCK9 (KEY5)."]
pub mod rd_key5_data1;
#[doc = "RD_KEY5_DATA2 (r) register accessor: Register $n of BLOCK9 (KEY5).\n\nYou can [`read`](crate::Reg::read) this register and get [`rd_key5_data2::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@rd_key5_data2`] module"]
pub type RD_KEY5_DATA2 = crate::Reg<rd_key5_data2::RD_KEY5_DATA2_SPEC>;
#[doc = "Register $n of BLOCK9 (KEY5)."]
pub mod rd_key5_data2;
#[doc = "RD_KEY5_DATA3 (r) register accessor: Register $n of BLOCK9 (KEY5).\n\nYou can [`read`](crate::Reg::read) this register and get [`rd_key5_data3::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@rd_key5_data3`] module"]
pub type RD_KEY5_DATA3 = crate::Reg<rd_key5_data3::RD_KEY5_DATA3_SPEC>;
#[doc = "Register $n of BLOCK9 (KEY5)."]
pub mod rd_key5_data3;
#[doc = "RD_KEY5_DATA4 (r) register accessor: Register $n of BLOCK9 (KEY5).\n\nYou can [`read`](crate::Reg::read) this register and get [`rd_key5_data4::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@rd_key5_data4`] module"]
pub type RD_KEY5_DATA4 = crate::Reg<rd_key5_data4::RD_KEY5_DATA4_SPEC>;
#[doc = "Register $n of BLOCK9 (KEY5)."]
pub mod rd_key5_data4;
#[doc = "RD_KEY5_DATA5 (r) register accessor: Register $n of BLOCK9 (KEY5).\n\nYou can [`read`](crate::Reg::read) this register and get [`rd_key5_data5::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@rd_key5_data5`] module"]
pub type RD_KEY5_DATA5 = crate::Reg<rd_key5_data5::RD_KEY5_DATA5_SPEC>;
#[doc = "Register $n of BLOCK9 (KEY5)."]
pub mod rd_key5_data5;
#[doc = "RD_KEY5_DATA6 (r) register accessor: Register $n of BLOCK9 (KEY5).\n\nYou can [`read`](crate::Reg::read) this register and get [`rd_key5_data6::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@rd_key5_data6`] module"]
pub type RD_KEY5_DATA6 = crate::Reg<rd_key5_data6::RD_KEY5_DATA6_SPEC>;
#[doc = "Register $n of BLOCK9 (KEY5)."]
pub mod rd_key5_data6;
#[doc = "RD_KEY5_DATA7 (r) register accessor: Register $n of BLOCK9 (KEY5).\n\nYou can [`read`](crate::Reg::read) this register and get [`rd_key5_data7::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@rd_key5_data7`] module"]
pub type RD_KEY5_DATA7 = crate::Reg<rd_key5_data7::RD_KEY5_DATA7_SPEC>;
#[doc = "Register $n of BLOCK9 (KEY5)."]
pub mod rd_key5_data7;
#[doc = "RD_SYS_PART2_DATA0 (r) register accessor: Register $n of BLOCK10 (system).\n\nYou can [`read`](crate::Reg::read) this register and get [`rd_sys_part2_data0::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@rd_sys_part2_data0`] module"]
pub type RD_SYS_PART2_DATA0 = crate::Reg<rd_sys_part2_data0::RD_SYS_PART2_DATA0_SPEC>;
#[doc = "Register $n of BLOCK10 (system)."]
pub mod rd_sys_part2_data0;
#[doc = "RD_SYS_PART2_DATA1 (r) register accessor: Register $n of BLOCK9 (KEY5).\n\nYou can [`read`](crate::Reg::read) this register and get [`rd_sys_part2_data1::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@rd_sys_part2_data1`] module"]
pub type RD_SYS_PART2_DATA1 = crate::Reg<rd_sys_part2_data1::RD_SYS_PART2_DATA1_SPEC>;
#[doc = "Register $n of BLOCK9 (KEY5)."]
pub mod rd_sys_part2_data1;
#[doc = "RD_SYS_PART2_DATA2 (r) register accessor: Register $n of BLOCK10 (system).\n\nYou can [`read`](crate::Reg::read) this register and get [`rd_sys_part2_data2::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@rd_sys_part2_data2`] module"]
pub type RD_SYS_PART2_DATA2 = crate::Reg<rd_sys_part2_data2::RD_SYS_PART2_DATA2_SPEC>;
#[doc = "Register $n of BLOCK10 (system)."]
pub mod rd_sys_part2_data2;
#[doc = "RD_SYS_PART2_DATA3 (r) register accessor: Register $n of BLOCK10 (system).\n\nYou can [`read`](crate::Reg::read) this register and get [`rd_sys_part2_data3::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@rd_sys_part2_data3`] module"]
pub type RD_SYS_PART2_DATA3 = crate::Reg<rd_sys_part2_data3::RD_SYS_PART2_DATA3_SPEC>;
#[doc = "Register $n of BLOCK10 (system)."]
pub mod rd_sys_part2_data3;
#[doc = "RD_SYS_PART2_DATA4 (r) register accessor: Register $n of BLOCK10 (system).\n\nYou can [`read`](crate::Reg::read) this register and get [`rd_sys_part2_data4::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@rd_sys_part2_data4`] module"]
pub type RD_SYS_PART2_DATA4 = crate::Reg<rd_sys_part2_data4::RD_SYS_PART2_DATA4_SPEC>;
#[doc = "Register $n of BLOCK10 (system)."]
pub mod rd_sys_part2_data4;
#[doc = "RD_SYS_PART2_DATA5 (r) register accessor: Register $n of BLOCK10 (system).\n\nYou can [`read`](crate::Reg::read) this register and get [`rd_sys_part2_data5::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@rd_sys_part2_data5`] module"]
pub type RD_SYS_PART2_DATA5 = crate::Reg<rd_sys_part2_data5::RD_SYS_PART2_DATA5_SPEC>;
#[doc = "Register $n of BLOCK10 (system)."]
pub mod rd_sys_part2_data5;
#[doc = "RD_SYS_PART2_DATA6 (r) register accessor: Register $n of BLOCK10 (system).\n\nYou can [`read`](crate::Reg::read) this register and get [`rd_sys_part2_data6::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@rd_sys_part2_data6`] module"]
pub type RD_SYS_PART2_DATA6 = crate::Reg<rd_sys_part2_data6::RD_SYS_PART2_DATA6_SPEC>;
#[doc = "Register $n of BLOCK10 (system)."]
pub mod rd_sys_part2_data6;
#[doc = "RD_SYS_PART2_DATA7 (r) register accessor: Register $n of BLOCK10 (system).\n\nYou can [`read`](crate::Reg::read) this register and get [`rd_sys_part2_data7::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@rd_sys_part2_data7`] module"]
pub type RD_SYS_PART2_DATA7 = crate::Reg<rd_sys_part2_data7::RD_SYS_PART2_DATA7_SPEC>;
#[doc = "Register $n of BLOCK10 (system)."]
pub mod rd_sys_part2_data7;
#[doc = "RD_REPEAT_ERR0 (r) register accessor: Programming error record register 0 of BLOCK0.\n\nYou can [`read`](crate::Reg::read) this register and get [`rd_repeat_err0::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@rd_repeat_err0`] module"]
pub type RD_REPEAT_ERR0 = crate::Reg<rd_repeat_err0::RD_REPEAT_ERR0_SPEC>;
#[doc = "Programming error record register 0 of BLOCK0."]
pub mod rd_repeat_err0;
#[doc = "RD_REPEAT_ERR1 (r) register accessor: Programming error record register 1 of BLOCK0.\n\nYou can [`read`](crate::Reg::read) this register and get [`rd_repeat_err1::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@rd_repeat_err1`] module"]
pub type RD_REPEAT_ERR1 = crate::Reg<rd_repeat_err1::RD_REPEAT_ERR1_SPEC>;
#[doc = "Programming error record register 1 of BLOCK0."]
pub mod rd_repeat_err1;
#[doc = "RD_REPEAT_ERR2 (r) register accessor: Programming error record register 2 of BLOCK0.\n\nYou can [`read`](crate::Reg::read) this register and get [`rd_repeat_err2::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@rd_repeat_err2`] module"]
pub type RD_REPEAT_ERR2 = crate::Reg<rd_repeat_err2::RD_REPEAT_ERR2_SPEC>;
#[doc = "Programming error record register 2 of BLOCK0."]
pub mod rd_repeat_err2;
#[doc = "RD_REPEAT_ERR3 (r) register accessor: Programming error record register 3 of BLOCK0.\n\nYou can [`read`](crate::Reg::read) this register and get [`rd_repeat_err3::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@rd_repeat_err3`] module"]
pub type RD_REPEAT_ERR3 = crate::Reg<rd_repeat_err3::RD_REPEAT_ERR3_SPEC>;
#[doc = "Programming error record register 3 of BLOCK0."]
pub mod rd_repeat_err3;
#[doc = "RD_REPEAT_ERR4 (r) register accessor: Programming error record register 4 of BLOCK0.\n\nYou can [`read`](crate::Reg::read) this register and get [`rd_repeat_err4::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@rd_repeat_err4`] module"]
pub type RD_REPEAT_ERR4 = crate::Reg<rd_repeat_err4::RD_REPEAT_ERR4_SPEC>;
#[doc = "Programming error record register 4 of BLOCK0."]
pub mod rd_repeat_err4;
#[doc = "RD_RS_ERR0 (r) register accessor: Programming error record register 0 of BLOCK1-10.\n\nYou can [`read`](crate::Reg::read) this register and get [`rd_rs_err0::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@rd_rs_err0`] module"]
pub type RD_RS_ERR0 = crate::Reg<rd_rs_err0::RD_RS_ERR0_SPEC>;
#[doc = "Programming error record register 0 of BLOCK1-10."]
pub mod rd_rs_err0;
#[doc = "RD_RS_ERR1 (r) register accessor: Programming error record register 1 of BLOCK1-10.\n\nYou can [`read`](crate::Reg::read) this register and get [`rd_rs_err1::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@rd_rs_err1`] module"]
pub type RD_RS_ERR1 = crate::Reg<rd_rs_err1::RD_RS_ERR1_SPEC>;
#[doc = "Programming error record register 1 of BLOCK1-10."]
pub mod rd_rs_err1;
#[doc = "CLK (rw) register accessor: eFuse clcok configuration register.\n\nYou can [`read`](crate::Reg::read) this register and get [`clk::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`clk::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@clk`] module"]
pub type CLK = crate::Reg<clk::CLK_SPEC>;
#[doc = "eFuse clcok configuration register."]
pub mod clk;
#[doc = "CONF (rw) register accessor: eFuse operation mode configuraiton register\n\nYou can [`read`](crate::Reg::read) this register and get [`conf::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`conf::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@conf`] module"]
pub type CONF = crate::Reg<conf::CONF_SPEC>;
#[doc = "eFuse operation mode configuraiton register"]
pub mod conf;
#[doc = "STATUS (r) register accessor: eFuse status register.\n\nYou can [`read`](crate::Reg::read) this register and get [`status::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@status`] module"]
pub type STATUS = crate::Reg<status::STATUS_SPEC>;
#[doc = "eFuse status register."]
pub mod status;
#[doc = "CMD (rw) register accessor: eFuse command register.\n\nYou can [`read`](crate::Reg::read) this register and get [`cmd::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`cmd::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@cmd`] module"]
pub type CMD = crate::Reg<cmd::CMD_SPEC>;
#[doc = "eFuse command register."]
pub mod cmd;
#[doc = "INT_RAW (r) register accessor: eFuse raw interrupt register.\n\nYou can [`read`](crate::Reg::read) this register and get [`int_raw::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@int_raw`] module"]
pub type INT_RAW = crate::Reg<int_raw::INT_RAW_SPEC>;
#[doc = "eFuse raw interrupt register."]
pub mod int_raw;
#[doc = "INT_ST (r) register accessor: eFuse interrupt status register.\n\nYou can [`read`](crate::Reg::read) this register and get [`int_st::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@int_st`] module"]
pub type INT_ST = crate::Reg<int_st::INT_ST_SPEC>;
#[doc = "eFuse interrupt status register."]
pub mod int_st;
#[doc = "INT_ENA (rw) register accessor: eFuse interrupt enable register.\n\nYou can [`read`](crate::Reg::read) this register and get [`int_ena::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`int_ena::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@int_ena`] module"]
pub type INT_ENA = crate::Reg<int_ena::INT_ENA_SPEC>;
#[doc = "eFuse interrupt enable register."]
pub mod int_ena;
#[doc = "INT_CLR (w) register accessor: eFuse interrupt clear register.\n\nYou can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`int_clr::W`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@int_clr`] module"]
pub type INT_CLR = crate::Reg<int_clr::INT_CLR_SPEC>;
#[doc = "eFuse interrupt clear register."]
pub mod int_clr;
#[doc = "DAC_CONF (rw) register accessor: Controls the eFuse programming voltage.\n\nYou can [`read`](crate::Reg::read) this register and get [`dac_conf::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`dac_conf::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@dac_conf`] module"]
pub type DAC_CONF = crate::Reg<dac_conf::DAC_CONF_SPEC>;
#[doc = "Controls the eFuse programming voltage."]
pub mod dac_conf;
#[doc = "RD_TIM_CONF (rw) register accessor: Configures read timing parameters.\n\nYou can [`read`](crate::Reg::read) this register and get [`rd_tim_conf::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`rd_tim_conf::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@rd_tim_conf`] module"]
pub type RD_TIM_CONF = crate::Reg<rd_tim_conf::RD_TIM_CONF_SPEC>;
#[doc = "Configures read timing parameters."]
pub mod rd_tim_conf;
#[doc = "WR_TIM_CONF1 (rw) register accessor: Configurarion register 1 of eFuse programming timing parameters.\n\nYou can [`read`](crate::Reg::read) this register and get [`wr_tim_conf1::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`wr_tim_conf1::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@wr_tim_conf1`] module"]
pub type WR_TIM_CONF1 = crate::Reg<wr_tim_conf1::WR_TIM_CONF1_SPEC>;
#[doc = "Configurarion register 1 of eFuse programming timing parameters."]
pub mod wr_tim_conf1;
#[doc = "WR_TIM_CONF2 (rw) register accessor: Configurarion register 2 of eFuse programming timing parameters.\n\nYou can [`read`](crate::Reg::read) this register and get [`wr_tim_conf2::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`wr_tim_conf2::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@wr_tim_conf2`] module"]
pub type WR_TIM_CONF2 = crate::Reg<wr_tim_conf2::WR_TIM_CONF2_SPEC>;
#[doc = "Configurarion register 2 of eFuse programming timing parameters."]
pub mod wr_tim_conf2;
#[doc = "WR_TIM_CONF0_RS_BYPASS (rw) register accessor: Configurarion register0 of eFuse programming time parameters and rs bypass operation.\n\nYou can [`read`](crate::Reg::read) this register and get [`wr_tim_conf0_rs_bypass::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`wr_tim_conf0_rs_bypass::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@wr_tim_conf0_rs_bypass`] module"]
pub type WR_TIM_CONF0_RS_BYPASS = crate::Reg<wr_tim_conf0_rs_bypass::WR_TIM_CONF0_RS_BYPASS_SPEC>;
#[doc = "Configurarion register0 of eFuse programming time parameters and rs bypass operation."]
pub mod wr_tim_conf0_rs_bypass;
pub use crate::aes::{date, DATE};
