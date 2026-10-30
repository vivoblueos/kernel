#[doc = "Register `CH%s_TX_LIM` reader"]
pub type R = crate::R<CH_TX_LIM_SPEC>;
#[doc = "Register `CH%s_TX_LIM` writer"]
pub type W = crate::W<CH_TX_LIM_SPEC>;
#[doc = "Field `TX_LIM` reader - This register is used to configure the maximum entries that CHANNEL%s can send out."]
pub type TX_LIM_R = crate::FieldReader<u16>;
#[doc = "Field `TX_LIM` writer - This register is used to configure the maximum entries that CHANNEL%s can send out."]
pub type TX_LIM_W<'a, REG> = crate::FieldWriter<'a, REG, 9, u16>;
#[doc = "Field `TX_LOOP_NUM` reader - This register is used to configure the maximum loop count when tx_conti_mode is valid."]
pub type TX_LOOP_NUM_R = crate::FieldReader<u16>;
#[doc = "Field `TX_LOOP_NUM` writer - This register is used to configure the maximum loop count when tx_conti_mode is valid."]
pub type TX_LOOP_NUM_W<'a, REG> = crate::FieldWriter<'a, REG, 10, u16>;
#[doc = "Field `TX_LOOP_CNT_EN` reader - This register is the enabled bit for loop count."]
pub type TX_LOOP_CNT_EN_R = crate::BitReader;
#[doc = "Field `TX_LOOP_CNT_EN` writer - This register is the enabled bit for loop count."]
pub type TX_LOOP_CNT_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `LOOP_COUNT_RESET` writer - This register is used to reset the loop count when tx_conti_mode is valid."]
pub type LOOP_COUNT_RESET_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `LOOP_STOP_EN` reader - This bit is used to enable the loop send stop function after the loop counter counts to loop number for CHANNEL%s."]
pub type LOOP_STOP_EN_R = crate::BitReader;
#[doc = "Field `LOOP_STOP_EN` writer - This bit is used to enable the loop send stop function after the loop counter counts to loop number for CHANNEL%s."]
pub type LOOP_STOP_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bits 0:8 - This register is used to configure the maximum entries that CHANNEL%s can send out."]
    #[inline(always)]
    pub fn tx_lim(&self) -> TX_LIM_R {
        TX_LIM_R::new((self.bits & 0x01ff) as u16)
    }
    #[doc = "Bits 9:18 - This register is used to configure the maximum loop count when tx_conti_mode is valid."]
    #[inline(always)]
    pub fn tx_loop_num(&self) -> TX_LOOP_NUM_R {
        TX_LOOP_NUM_R::new(((self.bits >> 9) & 0x03ff) as u16)
    }
    #[doc = "Bit 19 - This register is the enabled bit for loop count."]
    #[inline(always)]
    pub fn tx_loop_cnt_en(&self) -> TX_LOOP_CNT_EN_R {
        TX_LOOP_CNT_EN_R::new(((self.bits >> 19) & 1) != 0)
    }
    #[doc = "Bit 21 - This bit is used to enable the loop send stop function after the loop counter counts to loop number for CHANNEL%s."]
    #[inline(always)]
    pub fn loop_stop_en(&self) -> LOOP_STOP_EN_R {
        LOOP_STOP_EN_R::new(((self.bits >> 21) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("CH_TX_LIM")
            .field("tx_lim", &self.tx_lim())
            .field("tx_loop_num", &self.tx_loop_num())
            .field("tx_loop_cnt_en", &self.tx_loop_cnt_en())
            .field("loop_stop_en", &self.loop_stop_en())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:8 - This register is used to configure the maximum entries that CHANNEL%s can send out."]
    #[inline(always)]
    pub fn tx_lim(&mut self) -> TX_LIM_W<'_, CH_TX_LIM_SPEC> {
        TX_LIM_W::new(self, 0)
    }
    #[doc = "Bits 9:18 - This register is used to configure the maximum loop count when tx_conti_mode is valid."]
    #[inline(always)]
    pub fn tx_loop_num(&mut self) -> TX_LOOP_NUM_W<'_, CH_TX_LIM_SPEC> {
        TX_LOOP_NUM_W::new(self, 9)
    }
    #[doc = "Bit 19 - This register is the enabled bit for loop count."]
    #[inline(always)]
    pub fn tx_loop_cnt_en(&mut self) -> TX_LOOP_CNT_EN_W<'_, CH_TX_LIM_SPEC> {
        TX_LOOP_CNT_EN_W::new(self, 19)
    }
    #[doc = "Bit 20 - This register is used to reset the loop count when tx_conti_mode is valid."]
    #[inline(always)]
    pub fn loop_count_reset(&mut self) -> LOOP_COUNT_RESET_W<'_, CH_TX_LIM_SPEC> {
        LOOP_COUNT_RESET_W::new(self, 20)
    }
    #[doc = "Bit 21 - This bit is used to enable the loop send stop function after the loop counter counts to loop number for CHANNEL%s."]
    #[inline(always)]
    pub fn loop_stop_en(&mut self) -> LOOP_STOP_EN_W<'_, CH_TX_LIM_SPEC> {
        LOOP_STOP_EN_W::new(self, 21)
    }
}
#[doc = "Channel %s Tx event configuration register\n\nYou can [`read`](crate::Reg::read) this register and get [`ch_tx_lim::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`ch_tx_lim::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct CH_TX_LIM_SPEC;
impl crate::RegisterSpec for CH_TX_LIM_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`ch_tx_lim::R`](R) reader structure"]
impl crate::Readable for CH_TX_LIM_SPEC {}
#[doc = "`write(|w| ..)` method takes [`ch_tx_lim::W`](W) writer structure"]
impl crate::Writable for CH_TX_LIM_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets CH%s_TX_LIM to value 0x80"]
impl crate::Resettable for CH_TX_LIM_SPEC {
    const RESET_VALUE: u32 = 0x80;
}
