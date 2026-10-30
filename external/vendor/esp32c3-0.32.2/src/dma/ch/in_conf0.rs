#[doc = "Register `IN_CONF0` reader"]
pub type R = crate::R<IN_CONF0_SPEC>;
#[doc = "Register `IN_CONF0` writer"]
pub type W = crate::W<IN_CONF0_SPEC>;
#[doc = "Field `IN_RST` reader - This bit is used to reset DMA channel 0 Rx FSM and Rx FIFO pointer."]
pub type IN_RST_R = crate::BitReader;
#[doc = "Field `IN_RST` writer - This bit is used to reset DMA channel 0 Rx FSM and Rx FIFO pointer."]
pub type IN_RST_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `IN_LOOP_TEST` reader - reserved"]
pub type IN_LOOP_TEST_R = crate::BitReader;
#[doc = "Field `IN_LOOP_TEST` writer - reserved"]
pub type IN_LOOP_TEST_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `INDSCR_BURST_EN` reader - Set this bit to 1 to enable INCR burst transfer for Rx channel 0 reading link descriptor when accessing internal SRAM."]
pub type INDSCR_BURST_EN_R = crate::BitReader;
#[doc = "Field `INDSCR_BURST_EN` writer - Set this bit to 1 to enable INCR burst transfer for Rx channel 0 reading link descriptor when accessing internal SRAM."]
pub type INDSCR_BURST_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `IN_DATA_BURST_EN` reader - Set this bit to 1 to enable INCR burst transfer for Rx channel 0 receiving data when accessing internal SRAM."]
pub type IN_DATA_BURST_EN_R = crate::BitReader;
#[doc = "Field `IN_DATA_BURST_EN` writer - Set this bit to 1 to enable INCR burst transfer for Rx channel 0 receiving data when accessing internal SRAM."]
pub type IN_DATA_BURST_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `MEM_TRANS_EN` reader - Set this bit 1 to enable automatic transmitting data from memory to memory via DMA."]
pub type MEM_TRANS_EN_R = crate::BitReader;
#[doc = "Field `MEM_TRANS_EN` writer - Set this bit 1 to enable automatic transmitting data from memory to memory via DMA."]
pub type MEM_TRANS_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 0 - This bit is used to reset DMA channel 0 Rx FSM and Rx FIFO pointer."]
    #[inline(always)]
    pub fn in_rst(&self) -> IN_RST_R {
        IN_RST_R::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - reserved"]
    #[inline(always)]
    pub fn in_loop_test(&self) -> IN_LOOP_TEST_R {
        IN_LOOP_TEST_R::new(((self.bits >> 1) & 1) != 0)
    }
    #[doc = "Bit 2 - Set this bit to 1 to enable INCR burst transfer for Rx channel 0 reading link descriptor when accessing internal SRAM."]
    #[inline(always)]
    pub fn indscr_burst_en(&self) -> INDSCR_BURST_EN_R {
        INDSCR_BURST_EN_R::new(((self.bits >> 2) & 1) != 0)
    }
    #[doc = "Bit 3 - Set this bit to 1 to enable INCR burst transfer for Rx channel 0 receiving data when accessing internal SRAM."]
    #[inline(always)]
    pub fn in_data_burst_en(&self) -> IN_DATA_BURST_EN_R {
        IN_DATA_BURST_EN_R::new(((self.bits >> 3) & 1) != 0)
    }
    #[doc = "Bit 4 - Set this bit 1 to enable automatic transmitting data from memory to memory via DMA."]
    #[inline(always)]
    pub fn mem_trans_en(&self) -> MEM_TRANS_EN_R {
        MEM_TRANS_EN_R::new(((self.bits >> 4) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("IN_CONF0")
            .field("in_rst", &self.in_rst())
            .field("in_loop_test", &self.in_loop_test())
            .field("indscr_burst_en", &self.indscr_burst_en())
            .field("in_data_burst_en", &self.in_data_burst_en())
            .field("mem_trans_en", &self.mem_trans_en())
            .finish()
    }
}
impl W {
    #[doc = "Bit 0 - This bit is used to reset DMA channel 0 Rx FSM and Rx FIFO pointer."]
    #[inline(always)]
    pub fn in_rst(&mut self) -> IN_RST_W<'_, IN_CONF0_SPEC> {
        IN_RST_W::new(self, 0)
    }
    #[doc = "Bit 1 - reserved"]
    #[inline(always)]
    pub fn in_loop_test(&mut self) -> IN_LOOP_TEST_W<'_, IN_CONF0_SPEC> {
        IN_LOOP_TEST_W::new(self, 1)
    }
    #[doc = "Bit 2 - Set this bit to 1 to enable INCR burst transfer for Rx channel 0 reading link descriptor when accessing internal SRAM."]
    #[inline(always)]
    pub fn indscr_burst_en(&mut self) -> INDSCR_BURST_EN_W<'_, IN_CONF0_SPEC> {
        INDSCR_BURST_EN_W::new(self, 2)
    }
    #[doc = "Bit 3 - Set this bit to 1 to enable INCR burst transfer for Rx channel 0 receiving data when accessing internal SRAM."]
    #[inline(always)]
    pub fn in_data_burst_en(&mut self) -> IN_DATA_BURST_EN_W<'_, IN_CONF0_SPEC> {
        IN_DATA_BURST_EN_W::new(self, 3)
    }
    #[doc = "Bit 4 - Set this bit 1 to enable automatic transmitting data from memory to memory via DMA."]
    #[inline(always)]
    pub fn mem_trans_en(&mut self) -> MEM_TRANS_EN_W<'_, IN_CONF0_SPEC> {
        MEM_TRANS_EN_W::new(self, 4)
    }
}
#[doc = "DMA_IN_CONF0_CH0_REG.\n\nYou can [`read`](crate::Reg::read) this register and get [`in_conf0::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`in_conf0::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct IN_CONF0_SPEC;
impl crate::RegisterSpec for IN_CONF0_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`in_conf0::R`](R) reader structure"]
impl crate::Readable for IN_CONF0_SPEC {}
#[doc = "`write(|w| ..)` method takes [`in_conf0::W`](W) writer structure"]
impl crate::Writable for IN_CONF0_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets IN_CONF0 to value 0"]
impl crate::Resettable for IN_CONF0_SPEC {}
