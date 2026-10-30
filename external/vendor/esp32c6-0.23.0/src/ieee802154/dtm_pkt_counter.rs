#[doc = "Register `DTM_PKT_COUNTER` reader"]
pub type R = crate::R<DTM_PKT_COUNTER_SPEC>;
#[doc = "Register `DTM_PKT_COUNTER` writer"]
pub type W = crate::W<DTM_PKT_COUNTER_SPEC>;
#[doc = "Field `DTM_TXRX_PKT_COUNT` reader - "]
pub type DTM_TXRX_PKT_COUNT_R = crate::FieldReader<u16>;
#[doc = "Field `DTM_TXRX_PKT_COUNT` writer - "]
pub type DTM_TXRX_PKT_COUNT_W<'a, REG> = crate::FieldWriter<'a, REG, 16, u16>;
#[doc = "Field `DTM_CRC_ERR_PKT_COUNT` reader - "]
pub type DTM_CRC_ERR_PKT_COUNT_R = crate::FieldReader<u16>;
#[doc = "Field `DTM_CRC_ERR_PKT_COUNT` writer - "]
pub type DTM_CRC_ERR_PKT_COUNT_W<'a, REG> = crate::FieldWriter<'a, REG, 16, u16>;
impl R {
    #[doc = "Bits 0:15"]
    #[inline(always)]
    pub fn dtm_txrx_pkt_count(&self) -> DTM_TXRX_PKT_COUNT_R {
        DTM_TXRX_PKT_COUNT_R::new((self.bits & 0xffff) as u16)
    }
    #[doc = "Bits 16:31"]
    #[inline(always)]
    pub fn dtm_crc_err_pkt_count(&self) -> DTM_CRC_ERR_PKT_COUNT_R {
        DTM_CRC_ERR_PKT_COUNT_R::new(((self.bits >> 16) & 0xffff) as u16)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("DTM_PKT_COUNTER")
            .field("dtm_txrx_pkt_count", &self.dtm_txrx_pkt_count())
            .field("dtm_crc_err_pkt_count", &self.dtm_crc_err_pkt_count())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:15"]
    #[inline(always)]
    pub fn dtm_txrx_pkt_count(&mut self) -> DTM_TXRX_PKT_COUNT_W<'_, DTM_PKT_COUNTER_SPEC> {
        DTM_TXRX_PKT_COUNT_W::new(self, 0)
    }
    #[doc = "Bits 16:31"]
    #[inline(always)]
    pub fn dtm_crc_err_pkt_count(&mut self) -> DTM_CRC_ERR_PKT_COUNT_W<'_, DTM_PKT_COUNTER_SPEC> {
        DTM_CRC_ERR_PKT_COUNT_W::new(self, 16)
    }
}
#[doc = "\n\nYou can [`read`](crate::Reg::read) this register and get [`dtm_pkt_counter::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`dtm_pkt_counter::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct DTM_PKT_COUNTER_SPEC;
impl crate::RegisterSpec for DTM_PKT_COUNTER_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`dtm_pkt_counter::R`](R) reader structure"]
impl crate::Readable for DTM_PKT_COUNTER_SPEC {}
#[doc = "`write(|w| ..)` method takes [`dtm_pkt_counter::W`](W) writer structure"]
impl crate::Writable for DTM_PKT_COUNTER_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets DTM_PKT_COUNTER to value 0"]
impl crate::Resettable for DTM_PKT_COUNTER_SPEC {}
