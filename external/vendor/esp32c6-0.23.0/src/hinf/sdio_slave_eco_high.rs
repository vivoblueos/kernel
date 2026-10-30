#[doc = "Register `SDIO_SLAVE_ECO_HIGH` reader"]
pub type R = crate::R<SDIO_SLAVE_ECO_HIGH_SPEC>;
#[doc = "Register `SDIO_SLAVE_ECO_HIGH` writer"]
pub type W = crate::W<SDIO_SLAVE_ECO_HIGH_SPEC>;
#[doc = "Field `RDN_ECO_HIGH` reader - redundant registers for sdio_slave"]
pub type RDN_ECO_HIGH_R = crate::FieldReader<u32>;
#[doc = "Field `RDN_ECO_HIGH` writer - redundant registers for sdio_slave"]
pub type RDN_ECO_HIGH_W<'a, REG> = crate::FieldWriter<'a, REG, 32, u32>;
impl R {
    #[doc = "Bits 0:31 - redundant registers for sdio_slave"]
    #[inline(always)]
    pub fn rdn_eco_high(&self) -> RDN_ECO_HIGH_R {
        RDN_ECO_HIGH_R::new(self.bits)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("SDIO_SLAVE_ECO_HIGH")
            .field("rdn_eco_high", &self.rdn_eco_high())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:31 - redundant registers for sdio_slave"]
    #[inline(always)]
    pub fn rdn_eco_high(&mut self) -> RDN_ECO_HIGH_W<'_, SDIO_SLAVE_ECO_HIGH_SPEC> {
        RDN_ECO_HIGH_W::new(self, 0)
    }
}
#[doc = "sdio_slave redundant control registers\n\nYou can [`read`](crate::Reg::read) this register and get [`sdio_slave_eco_high::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`sdio_slave_eco_high::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct SDIO_SLAVE_ECO_HIGH_SPEC;
impl crate::RegisterSpec for SDIO_SLAVE_ECO_HIGH_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`sdio_slave_eco_high::R`](R) reader structure"]
impl crate::Readable for SDIO_SLAVE_ECO_HIGH_SPEC {}
#[doc = "`write(|w| ..)` method takes [`sdio_slave_eco_high::W`](W) writer structure"]
impl crate::Writable for SDIO_SLAVE_ECO_HIGH_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets SDIO_SLAVE_ECO_HIGH to value 0xffff_ffff"]
impl crate::Resettable for SDIO_SLAVE_ECO_HIGH_SPEC {
    const RESET_VALUE: u32 = 0xffff_ffff;
}
