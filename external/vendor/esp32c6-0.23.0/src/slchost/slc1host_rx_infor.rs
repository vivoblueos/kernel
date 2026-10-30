#[doc = "Register `SLC1HOST_RX_INFOR` reader"]
pub type R = crate::R<SLC1HOST_RX_INFOR_SPEC>;
#[doc = "Register `SLC1HOST_RX_INFOR` writer"]
pub type W = crate::W<SLC1HOST_RX_INFOR_SPEC>;
#[doc = "Field `SLC1HOST_RX_INFOR` reader - *******Description***********"]
pub type SLC1HOST_RX_INFOR_R = crate::FieldReader<u32>;
#[doc = "Field `SLC1HOST_RX_INFOR` writer - *******Description***********"]
pub type SLC1HOST_RX_INFOR_W<'a, REG> = crate::FieldWriter<'a, REG, 20, u32>;
impl R {
    #[doc = "Bits 0:19 - *******Description***********"]
    #[inline(always)]
    pub fn slc1host_rx_infor(&self) -> SLC1HOST_RX_INFOR_R {
        SLC1HOST_RX_INFOR_R::new(self.bits & 0x000f_ffff)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("SLC1HOST_RX_INFOR")
            .field("slc1host_rx_infor", &self.slc1host_rx_infor())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:19 - *******Description***********"]
    #[inline(always)]
    pub fn slc1host_rx_infor(&mut self) -> SLC1HOST_RX_INFOR_W<'_, SLC1HOST_RX_INFOR_SPEC> {
        SLC1HOST_RX_INFOR_W::new(self, 0)
    }
}
#[doc = "*******Description***********\n\nYou can [`read`](crate::Reg::read) this register and get [`slc1host_rx_infor::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`slc1host_rx_infor::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct SLC1HOST_RX_INFOR_SPEC;
impl crate::RegisterSpec for SLC1HOST_RX_INFOR_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`slc1host_rx_infor::R`](R) reader structure"]
impl crate::Readable for SLC1HOST_RX_INFOR_SPEC {}
#[doc = "`write(|w| ..)` method takes [`slc1host_rx_infor::W`](W) writer structure"]
impl crate::Writable for SLC1HOST_RX_INFOR_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets SLC1HOST_RX_INFOR to value 0"]
impl crate::Resettable for SLC1HOST_RX_INFOR_SPEC {}
