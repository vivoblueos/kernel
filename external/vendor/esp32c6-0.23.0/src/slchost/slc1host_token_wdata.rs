#[doc = "Register `SLC1HOST_TOKEN_WDATA` reader"]
pub type R = crate::R<SLC1HOST_TOKEN_WDATA_SPEC>;
#[doc = "Register `SLC1HOST_TOKEN_WDATA` writer"]
pub type W = crate::W<SLC1HOST_TOKEN_WDATA_SPEC>;
#[doc = "Field `SLC1HOST_TOKEN0_WD` reader - *******Description***********"]
pub type SLC1HOST_TOKEN0_WD_R = crate::FieldReader<u16>;
#[doc = "Field `SLC1HOST_TOKEN0_WD` writer - *******Description***********"]
pub type SLC1HOST_TOKEN0_WD_W<'a, REG> = crate::FieldWriter<'a, REG, 12, u16>;
#[doc = "Field `SLC1HOST_TOKEN1_WD` reader - *******Description***********"]
pub type SLC1HOST_TOKEN1_WD_R = crate::FieldReader<u16>;
#[doc = "Field `SLC1HOST_TOKEN1_WD` writer - *******Description***********"]
pub type SLC1HOST_TOKEN1_WD_W<'a, REG> = crate::FieldWriter<'a, REG, 12, u16>;
impl R {
    #[doc = "Bits 0:11 - *******Description***********"]
    #[inline(always)]
    pub fn slc1host_token0_wd(&self) -> SLC1HOST_TOKEN0_WD_R {
        SLC1HOST_TOKEN0_WD_R::new((self.bits & 0x0fff) as u16)
    }
    #[doc = "Bits 16:27 - *******Description***********"]
    #[inline(always)]
    pub fn slc1host_token1_wd(&self) -> SLC1HOST_TOKEN1_WD_R {
        SLC1HOST_TOKEN1_WD_R::new(((self.bits >> 16) & 0x0fff) as u16)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("SLC1HOST_TOKEN_WDATA")
            .field("slc1host_token0_wd", &self.slc1host_token0_wd())
            .field("slc1host_token1_wd", &self.slc1host_token1_wd())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:11 - *******Description***********"]
    #[inline(always)]
    pub fn slc1host_token0_wd(&mut self) -> SLC1HOST_TOKEN0_WD_W<'_, SLC1HOST_TOKEN_WDATA_SPEC> {
        SLC1HOST_TOKEN0_WD_W::new(self, 0)
    }
    #[doc = "Bits 16:27 - *******Description***********"]
    #[inline(always)]
    pub fn slc1host_token1_wd(&mut self) -> SLC1HOST_TOKEN1_WD_W<'_, SLC1HOST_TOKEN_WDATA_SPEC> {
        SLC1HOST_TOKEN1_WD_W::new(self, 16)
    }
}
#[doc = "*******Description***********\n\nYou can [`read`](crate::Reg::read) this register and get [`slc1host_token_wdata::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`slc1host_token_wdata::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct SLC1HOST_TOKEN_WDATA_SPEC;
impl crate::RegisterSpec for SLC1HOST_TOKEN_WDATA_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`slc1host_token_wdata::R`](R) reader structure"]
impl crate::Readable for SLC1HOST_TOKEN_WDATA_SPEC {}
#[doc = "`write(|w| ..)` method takes [`slc1host_token_wdata::W`](W) writer structure"]
impl crate::Writable for SLC1HOST_TOKEN_WDATA_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets SLC1HOST_TOKEN_WDATA to value 0"]
impl crate::Resettable for SLC1HOST_TOKEN_WDATA_SPEC {}
