#[doc = "Register `RCD_EN` reader"]
pub type R = crate::R<RCD_EN_SPEC>;
#[doc = "Register `RCD_EN` writer"]
pub type W = crate::W<RCD_EN_SPEC>;
#[doc = "Field `RCD_RECORDEN` reader - reg_core_0_rcd_recorden"]
pub type RCD_RECORDEN_R = crate::BitReader;
#[doc = "Field `RCD_RECORDEN` writer - reg_core_0_rcd_recorden"]
pub type RCD_RECORDEN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `RCD_PDEBUGEN` reader - reg_core_0_rcd_pdebugen"]
pub type RCD_PDEBUGEN_R = crate::BitReader;
#[doc = "Field `RCD_PDEBUGEN` writer - reg_core_0_rcd_pdebugen"]
pub type RCD_PDEBUGEN_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 0 - reg_core_0_rcd_recorden"]
    #[inline(always)]
    pub fn rcd_recorden(&self) -> RCD_RECORDEN_R {
        RCD_RECORDEN_R::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - reg_core_0_rcd_pdebugen"]
    #[inline(always)]
    pub fn rcd_pdebugen(&self) -> RCD_PDEBUGEN_R {
        RCD_PDEBUGEN_R::new(((self.bits >> 1) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("RCD_EN")
            .field("rcd_recorden", &self.rcd_recorden())
            .field("rcd_pdebugen", &self.rcd_pdebugen())
            .finish()
    }
}
impl W {
    #[doc = "Bit 0 - reg_core_0_rcd_recorden"]
    #[inline(always)]
    pub fn rcd_recorden(&mut self) -> RCD_RECORDEN_W<'_, RCD_EN_SPEC> {
        RCD_RECORDEN_W::new(self, 0)
    }
    #[doc = "Bit 1 - reg_core_0_rcd_pdebugen"]
    #[inline(always)]
    pub fn rcd_pdebugen(&mut self) -> RCD_PDEBUGEN_W<'_, RCD_EN_SPEC> {
        RCD_PDEBUGEN_W::new(self, 1)
    }
}
#[doc = "ASSIST_DEBUG_CORE_0_RCD_EN_REG\n\nYou can [`read`](crate::Reg::read) this register and get [`rcd_en::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`rcd_en::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct RCD_EN_SPEC;
impl crate::RegisterSpec for RCD_EN_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`rcd_en::R`](R) reader structure"]
impl crate::Readable for RCD_EN_SPEC {}
#[doc = "`write(|w| ..)` method takes [`rcd_en::W`](W) writer structure"]
impl crate::Writable for RCD_EN_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets RCD_EN to value 0"]
impl crate::Resettable for RCD_EN_SPEC {}
