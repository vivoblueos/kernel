#[doc = "Register `TX_CFG0` reader"]
pub type R = crate::R<TX_CFG0_SPEC>;
#[doc = "Register `TX_CFG0` writer"]
pub type W = crate::W<TX_CFG0_SPEC>;
#[doc = "Field `TX_BYTELEN` reader - Configures tx sending data byte length."]
pub type TX_BYTELEN_R = crate::FieldReader<u16>;
#[doc = "Field `TX_BYTELEN` writer - Configures tx sending data byte length."]
pub type TX_BYTELEN_W<'a, REG> = crate::FieldWriter<'a, REG, 16, u16>;
#[doc = "Field `TX_GATING_EN` reader - Write 1 to enable output tx clock gating."]
pub type TX_GATING_EN_R = crate::BitReader;
#[doc = "Field `TX_GATING_EN` writer - Write 1 to enable output tx clock gating."]
pub type TX_GATING_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `TX_START` reader - Write 1 to start tx global data output."]
pub type TX_START_R = crate::BitReader;
#[doc = "Field `TX_START` writer - Write 1 to start tx global data output."]
pub type TX_START_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `TX_HW_VALID_EN` reader - Write 1 to enable tx hardware data valid signal."]
pub type TX_HW_VALID_EN_R = crate::BitReader;
#[doc = "Field `TX_HW_VALID_EN` writer - Write 1 to enable tx hardware data valid signal."]
pub type TX_HW_VALID_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `TX_SMP_EDGE_SEL` reader - Write 0 to enable sampling data on the rising edge of tx clock. Write 0 to enable sampling data on the falling edge of tx clock."]
pub type TX_SMP_EDGE_SEL_R = crate::BitReader;
#[doc = "Field `TX_SMP_EDGE_SEL` writer - Write 0 to enable sampling data on the rising edge of tx clock. Write 0 to enable sampling data on the falling edge of tx clock."]
pub type TX_SMP_EDGE_SEL_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `TX_BIT_UNPACK_ORDER` reader - Write 0 to unpack bits from 1byte from MSB when data bus width is 4/2/1 bits. Write 0 to unpack bits from 1byte from LSB when data bus width is 4/2/1 bits."]
pub type TX_BIT_UNPACK_ORDER_R = crate::BitReader;
#[doc = "Field `TX_BIT_UNPACK_ORDER` writer - Write 0 to unpack bits from 1byte from MSB when data bus width is 4/2/1 bits. Write 0 to unpack bits from 1byte from LSB when data bus width is 4/2/1 bits."]
pub type TX_BIT_UNPACK_ORDER_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `TX_BUS_WID_SEL` reader - Tx data bus width selection. 100: bus width is 1 bit 011: bus width is 2 bits 010: bus width is 4 bits 001: bus width is 8 bits 000: bus width is 16 bits"]
pub type TX_BUS_WID_SEL_R = crate::FieldReader;
#[doc = "Field `TX_BUS_WID_SEL` writer - Tx data bus width selection. 100: bus width is 1 bit 011: bus width is 2 bits 010: bus width is 4 bits 001: bus width is 8 bits 000: bus width is 16 bits"]
pub type TX_BUS_WID_SEL_W<'a, REG> = crate::FieldWriter<'a, REG, 3>;
#[doc = "Field `TX_FIFO_SRST` reader - Write 1 to enable soft reset of async fifo in tx module."]
pub type TX_FIFO_SRST_R = crate::BitReader;
#[doc = "Field `TX_FIFO_SRST` writer - Write 1 to enable soft reset of async fifo in tx module."]
pub type TX_FIFO_SRST_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bits 2:17 - Configures tx sending data byte length."]
    #[inline(always)]
    pub fn tx_bytelen(&self) -> TX_BYTELEN_R {
        TX_BYTELEN_R::new(((self.bits >> 2) & 0xffff) as u16)
    }
    #[doc = "Bit 18 - Write 1 to enable output tx clock gating."]
    #[inline(always)]
    pub fn tx_gating_en(&self) -> TX_GATING_EN_R {
        TX_GATING_EN_R::new(((self.bits >> 18) & 1) != 0)
    }
    #[doc = "Bit 19 - Write 1 to start tx global data output."]
    #[inline(always)]
    pub fn tx_start(&self) -> TX_START_R {
        TX_START_R::new(((self.bits >> 19) & 1) != 0)
    }
    #[doc = "Bit 20 - Write 1 to enable tx hardware data valid signal."]
    #[inline(always)]
    pub fn tx_hw_valid_en(&self) -> TX_HW_VALID_EN_R {
        TX_HW_VALID_EN_R::new(((self.bits >> 20) & 1) != 0)
    }
    #[doc = "Bit 25 - Write 0 to enable sampling data on the rising edge of tx clock. Write 0 to enable sampling data on the falling edge of tx clock."]
    #[inline(always)]
    pub fn tx_smp_edge_sel(&self) -> TX_SMP_EDGE_SEL_R {
        TX_SMP_EDGE_SEL_R::new(((self.bits >> 25) & 1) != 0)
    }
    #[doc = "Bit 26 - Write 0 to unpack bits from 1byte from MSB when data bus width is 4/2/1 bits. Write 0 to unpack bits from 1byte from LSB when data bus width is 4/2/1 bits."]
    #[inline(always)]
    pub fn tx_bit_unpack_order(&self) -> TX_BIT_UNPACK_ORDER_R {
        TX_BIT_UNPACK_ORDER_R::new(((self.bits >> 26) & 1) != 0)
    }
    #[doc = "Bits 27:29 - Tx data bus width selection. 100: bus width is 1 bit 011: bus width is 2 bits 010: bus width is 4 bits 001: bus width is 8 bits 000: bus width is 16 bits"]
    #[inline(always)]
    pub fn tx_bus_wid_sel(&self) -> TX_BUS_WID_SEL_R {
        TX_BUS_WID_SEL_R::new(((self.bits >> 27) & 7) as u8)
    }
    #[doc = "Bit 30 - Write 1 to enable soft reset of async fifo in tx module."]
    #[inline(always)]
    pub fn tx_fifo_srst(&self) -> TX_FIFO_SRST_R {
        TX_FIFO_SRST_R::new(((self.bits >> 30) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("TX_CFG0")
            .field("tx_bytelen", &self.tx_bytelen())
            .field("tx_gating_en", &self.tx_gating_en())
            .field("tx_start", &self.tx_start())
            .field("tx_hw_valid_en", &self.tx_hw_valid_en())
            .field("tx_smp_edge_sel", &self.tx_smp_edge_sel())
            .field("tx_bit_unpack_order", &self.tx_bit_unpack_order())
            .field("tx_bus_wid_sel", &self.tx_bus_wid_sel())
            .field("tx_fifo_srst", &self.tx_fifo_srst())
            .finish()
    }
}
impl W {
    #[doc = "Bits 2:17 - Configures tx sending data byte length."]
    #[inline(always)]
    pub fn tx_bytelen(&mut self) -> TX_BYTELEN_W<'_, TX_CFG0_SPEC> {
        TX_BYTELEN_W::new(self, 2)
    }
    #[doc = "Bit 18 - Write 1 to enable output tx clock gating."]
    #[inline(always)]
    pub fn tx_gating_en(&mut self) -> TX_GATING_EN_W<'_, TX_CFG0_SPEC> {
        TX_GATING_EN_W::new(self, 18)
    }
    #[doc = "Bit 19 - Write 1 to start tx global data output."]
    #[inline(always)]
    pub fn tx_start(&mut self) -> TX_START_W<'_, TX_CFG0_SPEC> {
        TX_START_W::new(self, 19)
    }
    #[doc = "Bit 20 - Write 1 to enable tx hardware data valid signal."]
    #[inline(always)]
    pub fn tx_hw_valid_en(&mut self) -> TX_HW_VALID_EN_W<'_, TX_CFG0_SPEC> {
        TX_HW_VALID_EN_W::new(self, 20)
    }
    #[doc = "Bit 25 - Write 0 to enable sampling data on the rising edge of tx clock. Write 0 to enable sampling data on the falling edge of tx clock."]
    #[inline(always)]
    pub fn tx_smp_edge_sel(&mut self) -> TX_SMP_EDGE_SEL_W<'_, TX_CFG0_SPEC> {
        TX_SMP_EDGE_SEL_W::new(self, 25)
    }
    #[doc = "Bit 26 - Write 0 to unpack bits from 1byte from MSB when data bus width is 4/2/1 bits. Write 0 to unpack bits from 1byte from LSB when data bus width is 4/2/1 bits."]
    #[inline(always)]
    pub fn tx_bit_unpack_order(&mut self) -> TX_BIT_UNPACK_ORDER_W<'_, TX_CFG0_SPEC> {
        TX_BIT_UNPACK_ORDER_W::new(self, 26)
    }
    #[doc = "Bits 27:29 - Tx data bus width selection. 100: bus width is 1 bit 011: bus width is 2 bits 010: bus width is 4 bits 001: bus width is 8 bits 000: bus width is 16 bits"]
    #[inline(always)]
    pub fn tx_bus_wid_sel(&mut self) -> TX_BUS_WID_SEL_W<'_, TX_CFG0_SPEC> {
        TX_BUS_WID_SEL_W::new(self, 27)
    }
    #[doc = "Bit 30 - Write 1 to enable soft reset of async fifo in tx module."]
    #[inline(always)]
    pub fn tx_fifo_srst(&mut self) -> TX_FIFO_SRST_W<'_, TX_CFG0_SPEC> {
        TX_FIFO_SRST_W::new(self, 30)
    }
}
#[doc = "Parallel TX module configuration register0.\n\nYou can [`read`](crate::Reg::read) this register and get [`tx_cfg0::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`tx_cfg0::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct TX_CFG0_SPEC;
impl crate::RegisterSpec for TX_CFG0_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`tx_cfg0::R`](R) reader structure"]
impl crate::Readable for TX_CFG0_SPEC {}
#[doc = "`write(|w| ..)` method takes [`tx_cfg0::W`](W) writer structure"]
impl crate::Writable for TX_CFG0_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets TX_CFG0 to value 0"]
impl crate::Resettable for TX_CFG0_SPEC {}
