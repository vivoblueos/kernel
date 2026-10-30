#[doc = "Register `DTM_TX_PKT_CONFIG` reader"]
pub type R = crate::R<DTM_TX_PKT_CONFIG_SPEC>;
#[doc = "Register `DTM_TX_PKT_CONFIG` writer"]
pub type W = crate::W<DTM_TX_PKT_CONFIG_SPEC>;
#[doc = "Field `DTM_TX_PKT_THRESHOLD` reader - "]
pub type DTM_TX_PKT_THRESHOLD_R = crate::FieldReader<u16>;
#[doc = "Field `DTM_TX_PKT_THRESHOLD` writer - "]
pub type DTM_TX_PKT_THRESHOLD_W<'a, REG> = crate::FieldWriter<'a, REG, 16, u16>;
impl R {
    #[doc = "Bits 0:15"]
    #[inline(always)]
    pub fn dtm_tx_pkt_threshold(&self) -> DTM_TX_PKT_THRESHOLD_R {
        DTM_TX_PKT_THRESHOLD_R::new((self.bits & 0xffff) as u16)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("DTM_TX_PKT_CONFIG")
            .field("dtm_tx_pkt_threshold", &self.dtm_tx_pkt_threshold())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:15"]
    #[inline(always)]
    pub fn dtm_tx_pkt_threshold(&mut self) -> DTM_TX_PKT_THRESHOLD_W<'_, DTM_TX_PKT_CONFIG_SPEC> {
        DTM_TX_PKT_THRESHOLD_W::new(self, 0)
    }
}
#[doc = "\n\nYou can [`read`](crate::Reg::read) this register and get [`dtm_tx_pkt_config::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`dtm_tx_pkt_config::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct DTM_TX_PKT_CONFIG_SPEC;
impl crate::RegisterSpec for DTM_TX_PKT_CONFIG_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`dtm_tx_pkt_config::R`](R) reader structure"]
impl crate::Readable for DTM_TX_PKT_CONFIG_SPEC {}
#[doc = "`write(|w| ..)` method takes [`dtm_tx_pkt_config::W`](W) writer structure"]
impl crate::Writable for DTM_TX_PKT_CONFIG_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets DTM_TX_PKT_CONFIG to value 0"]
impl crate::Resettable for DTM_TX_PKT_CONFIG_SPEC {}
