#[doc = "Register `RX_CFG0` reader"]
pub type R = crate::R<RX_CFG0_SPEC>;
#[doc = "Register `RX_CFG0` writer"]
pub type W = crate::W<RX_CFG0_SPEC>;
#[doc = "Field `RX_EOF_GEN_SEL` reader - Write 0 to select eof generated manchnism by configured data byte length. Write 1 to select eof generated manchnism by external enable signal."]
pub type RX_EOF_GEN_SEL_R = crate::BitReader;
#[doc = "Field `RX_EOF_GEN_SEL` writer - Write 0 to select eof generated manchnism by configured data byte length. Write 1 to select eof generated manchnism by external enable signal."]
pub type RX_EOF_GEN_SEL_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `RX_START` reader - Write 1 to start rx global data sampling."]
pub type RX_START_R = crate::BitReader;
#[doc = "Field `RX_START` writer - Write 1 to start rx global data sampling."]
pub type RX_START_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `RX_DATA_BYTELEN` reader - Configures rx receieved data byte length."]
pub type RX_DATA_BYTELEN_R = crate::FieldReader<u16>;
#[doc = "Field `RX_DATA_BYTELEN` writer - Configures rx receieved data byte length."]
pub type RX_DATA_BYTELEN_W<'a, REG> = crate::FieldWriter<'a, REG, 16, u16>;
#[doc = "Field `RX_SW_EN` reader - Write 1 to enable software data sampling."]
pub type RX_SW_EN_R = crate::BitReader;
#[doc = "Field `RX_SW_EN` writer - Write 1 to enable software data sampling."]
pub type RX_SW_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `RX_PULSE_SUBMODE_SEL` reader - Pulse submode selection. 0000: positive pulse start(data bit included) && positive pulse end(data bit included) 0001: positive pulse start(data bit included) && positive pulse end (data bit excluded) 0010: positive pulse start(data bit excluded) && positive pulse end (data bit included) 0011: positive pulse start(data bit excluded) && positive pulse end (data bit excluded) 0100: positive pulse start(data bit included) && length end 0101: positive pulse start(data bit excluded) && length end 0110: negative pulse start(data bit included) && negative pulse end(data bit included) 0111: negative pulse start(data bit included) && negative pulse end (data bit excluded) 1000: negative pulse start(data bit excluded) && negative pulse end (data bit included) 1001: negative pulse start(data bit excluded) && negative pulse end (data bit excluded) 1010: negative pulse start(data bit included) && length end 1011: negative pulse start(data bit excluded) && length end"]
pub type RX_PULSE_SUBMODE_SEL_R = crate::FieldReader;
#[doc = "Field `RX_PULSE_SUBMODE_SEL` writer - Pulse submode selection. 0000: positive pulse start(data bit included) && positive pulse end(data bit included) 0001: positive pulse start(data bit included) && positive pulse end (data bit excluded) 0010: positive pulse start(data bit excluded) && positive pulse end (data bit included) 0011: positive pulse start(data bit excluded) && positive pulse end (data bit excluded) 0100: positive pulse start(data bit included) && length end 0101: positive pulse start(data bit excluded) && length end 0110: negative pulse start(data bit included) && negative pulse end(data bit included) 0111: negative pulse start(data bit included) && negative pulse end (data bit excluded) 1000: negative pulse start(data bit excluded) && negative pulse end (data bit included) 1001: negative pulse start(data bit excluded) && negative pulse end (data bit excluded) 1010: negative pulse start(data bit included) && length end 1011: negative pulse start(data bit excluded) && length end"]
pub type RX_PULSE_SUBMODE_SEL_W<'a, REG> = crate::FieldWriter<'a, REG, 4>;
#[doc = "Field `RX_LEVEL_SUBMODE_SEL` reader - Write 0 to sample data at high level of external enable signal. Write 1 to sample data at low level of external enable signal."]
pub type RX_LEVEL_SUBMODE_SEL_R = crate::BitReader;
#[doc = "Field `RX_LEVEL_SUBMODE_SEL` writer - Write 0 to sample data at high level of external enable signal. Write 1 to sample data at low level of external enable signal."]
pub type RX_LEVEL_SUBMODE_SEL_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `RX_SMP_MODE_SEL` reader - Rx data sampling mode selection. 000: external level enable mode 001: external pulse enable mode 010: internal software enable mode"]
pub type RX_SMP_MODE_SEL_R = crate::FieldReader;
#[doc = "Field `RX_SMP_MODE_SEL` writer - Rx data sampling mode selection. 000: external level enable mode 001: external pulse enable mode 010: internal software enable mode"]
pub type RX_SMP_MODE_SEL_W<'a, REG> = crate::FieldWriter<'a, REG, 2>;
#[doc = "Field `RX_CLK_EDGE_SEL` reader - Write 0 to enable sampling data on the rising edge of rx clock. Write 0 to enable sampling data on the falling edge of rx clock."]
pub type RX_CLK_EDGE_SEL_R = crate::BitReader;
#[doc = "Field `RX_CLK_EDGE_SEL` writer - Write 0 to enable sampling data on the rising edge of rx clock. Write 0 to enable sampling data on the falling edge of rx clock."]
pub type RX_CLK_EDGE_SEL_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `RX_BIT_PACK_ORDER` reader - Write 0 to pack bits into 1byte from MSB when data bus width is 4/2/1 bits. Write 0 to pack bits into 1byte from LSB when data bus width is 4/2/1 bits."]
pub type RX_BIT_PACK_ORDER_R = crate::BitReader;
#[doc = "Field `RX_BIT_PACK_ORDER` writer - Write 0 to pack bits into 1byte from MSB when data bus width is 4/2/1 bits. Write 0 to pack bits into 1byte from LSB when data bus width is 4/2/1 bits."]
pub type RX_BIT_PACK_ORDER_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `RX_BUS_WID_SEL` reader - Rx data bus width selection. 100: bus width is 1 bit 011: bus width is 2 bits 010: bus width is 4 bits 001: bus width is 8 bits 000: bus width is 16 bits"]
pub type RX_BUS_WID_SEL_R = crate::FieldReader;
#[doc = "Field `RX_BUS_WID_SEL` writer - Rx data bus width selection. 100: bus width is 1 bit 011: bus width is 2 bits 010: bus width is 4 bits 001: bus width is 8 bits 000: bus width is 16 bits"]
pub type RX_BUS_WID_SEL_W<'a, REG> = crate::FieldWriter<'a, REG, 3>;
#[doc = "Field `RX_FIFO_SRST` reader - Write 1 to enable soft reset of async fifo in rx module."]
pub type RX_FIFO_SRST_R = crate::BitReader;
#[doc = "Field `RX_FIFO_SRST` writer - Write 1 to enable soft reset of async fifo in rx module."]
pub type RX_FIFO_SRST_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 0 - Write 0 to select eof generated manchnism by configured data byte length. Write 1 to select eof generated manchnism by external enable signal."]
    #[inline(always)]
    pub fn rx_eof_gen_sel(&self) -> RX_EOF_GEN_SEL_R {
        RX_EOF_GEN_SEL_R::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - Write 1 to start rx global data sampling."]
    #[inline(always)]
    pub fn rx_start(&self) -> RX_START_R {
        RX_START_R::new(((self.bits >> 1) & 1) != 0)
    }
    #[doc = "Bits 2:17 - Configures rx receieved data byte length."]
    #[inline(always)]
    pub fn rx_data_bytelen(&self) -> RX_DATA_BYTELEN_R {
        RX_DATA_BYTELEN_R::new(((self.bits >> 2) & 0xffff) as u16)
    }
    #[doc = "Bit 18 - Write 1 to enable software data sampling."]
    #[inline(always)]
    pub fn rx_sw_en(&self) -> RX_SW_EN_R {
        RX_SW_EN_R::new(((self.bits >> 18) & 1) != 0)
    }
    #[doc = "Bits 19:22 - Pulse submode selection. 0000: positive pulse start(data bit included) && positive pulse end(data bit included) 0001: positive pulse start(data bit included) && positive pulse end (data bit excluded) 0010: positive pulse start(data bit excluded) && positive pulse end (data bit included) 0011: positive pulse start(data bit excluded) && positive pulse end (data bit excluded) 0100: positive pulse start(data bit included) && length end 0101: positive pulse start(data bit excluded) && length end 0110: negative pulse start(data bit included) && negative pulse end(data bit included) 0111: negative pulse start(data bit included) && negative pulse end (data bit excluded) 1000: negative pulse start(data bit excluded) && negative pulse end (data bit included) 1001: negative pulse start(data bit excluded) && negative pulse end (data bit excluded) 1010: negative pulse start(data bit included) && length end 1011: negative pulse start(data bit excluded) && length end"]
    #[inline(always)]
    pub fn rx_pulse_submode_sel(&self) -> RX_PULSE_SUBMODE_SEL_R {
        RX_PULSE_SUBMODE_SEL_R::new(((self.bits >> 19) & 0x0f) as u8)
    }
    #[doc = "Bit 23 - Write 0 to sample data at high level of external enable signal. Write 1 to sample data at low level of external enable signal."]
    #[inline(always)]
    pub fn rx_level_submode_sel(&self) -> RX_LEVEL_SUBMODE_SEL_R {
        RX_LEVEL_SUBMODE_SEL_R::new(((self.bits >> 23) & 1) != 0)
    }
    #[doc = "Bits 24:25 - Rx data sampling mode selection. 000: external level enable mode 001: external pulse enable mode 010: internal software enable mode"]
    #[inline(always)]
    pub fn rx_smp_mode_sel(&self) -> RX_SMP_MODE_SEL_R {
        RX_SMP_MODE_SEL_R::new(((self.bits >> 24) & 3) as u8)
    }
    #[doc = "Bit 26 - Write 0 to enable sampling data on the rising edge of rx clock. Write 0 to enable sampling data on the falling edge of rx clock."]
    #[inline(always)]
    pub fn rx_clk_edge_sel(&self) -> RX_CLK_EDGE_SEL_R {
        RX_CLK_EDGE_SEL_R::new(((self.bits >> 26) & 1) != 0)
    }
    #[doc = "Bit 27 - Write 0 to pack bits into 1byte from MSB when data bus width is 4/2/1 bits. Write 0 to pack bits into 1byte from LSB when data bus width is 4/2/1 bits."]
    #[inline(always)]
    pub fn rx_bit_pack_order(&self) -> RX_BIT_PACK_ORDER_R {
        RX_BIT_PACK_ORDER_R::new(((self.bits >> 27) & 1) != 0)
    }
    #[doc = "Bits 28:30 - Rx data bus width selection. 100: bus width is 1 bit 011: bus width is 2 bits 010: bus width is 4 bits 001: bus width is 8 bits 000: bus width is 16 bits"]
    #[inline(always)]
    pub fn rx_bus_wid_sel(&self) -> RX_BUS_WID_SEL_R {
        RX_BUS_WID_SEL_R::new(((self.bits >> 28) & 7) as u8)
    }
    #[doc = "Bit 31 - Write 1 to enable soft reset of async fifo in rx module."]
    #[inline(always)]
    pub fn rx_fifo_srst(&self) -> RX_FIFO_SRST_R {
        RX_FIFO_SRST_R::new(((self.bits >> 31) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("RX_CFG0")
            .field("rx_eof_gen_sel", &self.rx_eof_gen_sel())
            .field("rx_start", &self.rx_start())
            .field("rx_data_bytelen", &self.rx_data_bytelen())
            .field("rx_sw_en", &self.rx_sw_en())
            .field("rx_pulse_submode_sel", &self.rx_pulse_submode_sel())
            .field("rx_level_submode_sel", &self.rx_level_submode_sel())
            .field("rx_smp_mode_sel", &self.rx_smp_mode_sel())
            .field("rx_clk_edge_sel", &self.rx_clk_edge_sel())
            .field("rx_bit_pack_order", &self.rx_bit_pack_order())
            .field("rx_bus_wid_sel", &self.rx_bus_wid_sel())
            .field("rx_fifo_srst", &self.rx_fifo_srst())
            .finish()
    }
}
impl W {
    #[doc = "Bit 0 - Write 0 to select eof generated manchnism by configured data byte length. Write 1 to select eof generated manchnism by external enable signal."]
    #[inline(always)]
    pub fn rx_eof_gen_sel(&mut self) -> RX_EOF_GEN_SEL_W<'_, RX_CFG0_SPEC> {
        RX_EOF_GEN_SEL_W::new(self, 0)
    }
    #[doc = "Bit 1 - Write 1 to start rx global data sampling."]
    #[inline(always)]
    pub fn rx_start(&mut self) -> RX_START_W<'_, RX_CFG0_SPEC> {
        RX_START_W::new(self, 1)
    }
    #[doc = "Bits 2:17 - Configures rx receieved data byte length."]
    #[inline(always)]
    pub fn rx_data_bytelen(&mut self) -> RX_DATA_BYTELEN_W<'_, RX_CFG0_SPEC> {
        RX_DATA_BYTELEN_W::new(self, 2)
    }
    #[doc = "Bit 18 - Write 1 to enable software data sampling."]
    #[inline(always)]
    pub fn rx_sw_en(&mut self) -> RX_SW_EN_W<'_, RX_CFG0_SPEC> {
        RX_SW_EN_W::new(self, 18)
    }
    #[doc = "Bits 19:22 - Pulse submode selection. 0000: positive pulse start(data bit included) && positive pulse end(data bit included) 0001: positive pulse start(data bit included) && positive pulse end (data bit excluded) 0010: positive pulse start(data bit excluded) && positive pulse end (data bit included) 0011: positive pulse start(data bit excluded) && positive pulse end (data bit excluded) 0100: positive pulse start(data bit included) && length end 0101: positive pulse start(data bit excluded) && length end 0110: negative pulse start(data bit included) && negative pulse end(data bit included) 0111: negative pulse start(data bit included) && negative pulse end (data bit excluded) 1000: negative pulse start(data bit excluded) && negative pulse end (data bit included) 1001: negative pulse start(data bit excluded) && negative pulse end (data bit excluded) 1010: negative pulse start(data bit included) && length end 1011: negative pulse start(data bit excluded) && length end"]
    #[inline(always)]
    pub fn rx_pulse_submode_sel(&mut self) -> RX_PULSE_SUBMODE_SEL_W<'_, RX_CFG0_SPEC> {
        RX_PULSE_SUBMODE_SEL_W::new(self, 19)
    }
    #[doc = "Bit 23 - Write 0 to sample data at high level of external enable signal. Write 1 to sample data at low level of external enable signal."]
    #[inline(always)]
    pub fn rx_level_submode_sel(&mut self) -> RX_LEVEL_SUBMODE_SEL_W<'_, RX_CFG0_SPEC> {
        RX_LEVEL_SUBMODE_SEL_W::new(self, 23)
    }
    #[doc = "Bits 24:25 - Rx data sampling mode selection. 000: external level enable mode 001: external pulse enable mode 010: internal software enable mode"]
    #[inline(always)]
    pub fn rx_smp_mode_sel(&mut self) -> RX_SMP_MODE_SEL_W<'_, RX_CFG0_SPEC> {
        RX_SMP_MODE_SEL_W::new(self, 24)
    }
    #[doc = "Bit 26 - Write 0 to enable sampling data on the rising edge of rx clock. Write 0 to enable sampling data on the falling edge of rx clock."]
    #[inline(always)]
    pub fn rx_clk_edge_sel(&mut self) -> RX_CLK_EDGE_SEL_W<'_, RX_CFG0_SPEC> {
        RX_CLK_EDGE_SEL_W::new(self, 26)
    }
    #[doc = "Bit 27 - Write 0 to pack bits into 1byte from MSB when data bus width is 4/2/1 bits. Write 0 to pack bits into 1byte from LSB when data bus width is 4/2/1 bits."]
    #[inline(always)]
    pub fn rx_bit_pack_order(&mut self) -> RX_BIT_PACK_ORDER_W<'_, RX_CFG0_SPEC> {
        RX_BIT_PACK_ORDER_W::new(self, 27)
    }
    #[doc = "Bits 28:30 - Rx data bus width selection. 100: bus width is 1 bit 011: bus width is 2 bits 010: bus width is 4 bits 001: bus width is 8 bits 000: bus width is 16 bits"]
    #[inline(always)]
    pub fn rx_bus_wid_sel(&mut self) -> RX_BUS_WID_SEL_W<'_, RX_CFG0_SPEC> {
        RX_BUS_WID_SEL_W::new(self, 28)
    }
    #[doc = "Bit 31 - Write 1 to enable soft reset of async fifo in rx module."]
    #[inline(always)]
    pub fn rx_fifo_srst(&mut self) -> RX_FIFO_SRST_W<'_, RX_CFG0_SPEC> {
        RX_FIFO_SRST_W::new(self, 31)
    }
}
#[doc = "Parallel RX module configuration register0.\n\nYou can [`read`](crate::Reg::read) this register and get [`rx_cfg0::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`rx_cfg0::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct RX_CFG0_SPEC;
impl crate::RegisterSpec for RX_CFG0_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`rx_cfg0::R`](R) reader structure"]
impl crate::Readable for RX_CFG0_SPEC {}
#[doc = "`write(|w| ..)` method takes [`rx_cfg0::W`](W) writer structure"]
impl crate::Writable for RX_CFG0_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets RX_CFG0 to value 0"]
impl crate::Resettable for RX_CFG0_SPEC {}
