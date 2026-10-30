#[doc = "Register `TX_ERR_CNT` reader"]
pub type R = crate::R<TX_ERR_CNT_SPEC>;
#[doc = "Register `TX_ERR_CNT` writer"]
pub type W = crate::W<TX_ERR_CNT_SPEC>;
#[doc = "Field `TX_ERR_CNT` reader - The TX error counter register reflects the current value of the transmit error counter. Software has R/W permission in reset mode and RO in operation mode."]
pub type TX_ERR_CNT_R = crate::FieldReader;
#[doc = "Field `TX_ERR_CNT` writer - The TX error counter register reflects the current value of the transmit error counter. Software has R/W permission in reset mode and RO in operation mode."]
pub type TX_ERR_CNT_W<'a, REG> = crate::FieldWriter<'a, REG, 8>;
impl R {
    #[doc = "Bits 0:7 - The TX error counter register reflects the current value of the transmit error counter. Software has R/W permission in reset mode and RO in operation mode."]
    #[inline(always)]
    pub fn tx_err_cnt(&self) -> TX_ERR_CNT_R {
        TX_ERR_CNT_R::new((self.bits & 0xff) as u8)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("TX_ERR_CNT")
            .field("tx_err_cnt", &self.tx_err_cnt())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:7 - The TX error counter register reflects the current value of the transmit error counter. Software has R/W permission in reset mode and RO in operation mode."]
    #[inline(always)]
    pub fn tx_err_cnt(&mut self) -> TX_ERR_CNT_W<'_, TX_ERR_CNT_SPEC> {
        TX_ERR_CNT_W::new(self, 0)
    }
}
#[doc = "Tx error counter register.\n\nYou can [`read`](crate::Reg::read) this register and get [`tx_err_cnt::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`tx_err_cnt::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct TX_ERR_CNT_SPEC;
impl crate::RegisterSpec for TX_ERR_CNT_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`tx_err_cnt::R`](R) reader structure"]
impl crate::Readable for TX_ERR_CNT_SPEC {}
#[doc = "`write(|w| ..)` method takes [`tx_err_cnt::W`](W) writer structure"]
impl crate::Writable for TX_ERR_CNT_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets TX_ERR_CNT to value 0"]
impl crate::Resettable for TX_ERR_CNT_SPEC {}
