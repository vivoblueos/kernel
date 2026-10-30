#[doc = "Register `DEBUG_SEL0` reader"]
pub type R = crate::R<DEBUG_SEL0_SPEC>;
#[doc = "Register `DEBUG_SEL0` writer"]
pub type W = crate::W<DEBUG_SEL0_SPEC>;
#[doc = "Field `LP_DEBUG_SEL0` reader - need des"]
pub type LP_DEBUG_SEL0_R = crate::FieldReader;
#[doc = "Field `LP_DEBUG_SEL0` writer - need des"]
pub type LP_DEBUG_SEL0_W<'a, REG> = crate::FieldWriter<'a, REG, 7>;
#[doc = "Field `LP_DEBUG_SEL1` reader - need des"]
pub type LP_DEBUG_SEL1_R = crate::FieldReader;
#[doc = "Field `LP_DEBUG_SEL1` writer - need des"]
pub type LP_DEBUG_SEL1_W<'a, REG> = crate::FieldWriter<'a, REG, 7>;
#[doc = "Field `LP_DEBUG_SEL2` reader - need des"]
pub type LP_DEBUG_SEL2_R = crate::FieldReader;
#[doc = "Field `LP_DEBUG_SEL2` writer - need des"]
pub type LP_DEBUG_SEL2_W<'a, REG> = crate::FieldWriter<'a, REG, 7>;
#[doc = "Field `LP_DEBUG_SEL3` reader - need des"]
pub type LP_DEBUG_SEL3_R = crate::FieldReader;
#[doc = "Field `LP_DEBUG_SEL3` writer - need des"]
pub type LP_DEBUG_SEL3_W<'a, REG> = crate::FieldWriter<'a, REG, 7>;
impl R {
    #[doc = "Bits 0:6 - need des"]
    #[inline(always)]
    pub fn lp_debug_sel0(&self) -> LP_DEBUG_SEL0_R {
        LP_DEBUG_SEL0_R::new((self.bits & 0x7f) as u8)
    }
    #[doc = "Bits 7:13 - need des"]
    #[inline(always)]
    pub fn lp_debug_sel1(&self) -> LP_DEBUG_SEL1_R {
        LP_DEBUG_SEL1_R::new(((self.bits >> 7) & 0x7f) as u8)
    }
    #[doc = "Bits 14:20 - need des"]
    #[inline(always)]
    pub fn lp_debug_sel2(&self) -> LP_DEBUG_SEL2_R {
        LP_DEBUG_SEL2_R::new(((self.bits >> 14) & 0x7f) as u8)
    }
    #[doc = "Bits 21:27 - need des"]
    #[inline(always)]
    pub fn lp_debug_sel3(&self) -> LP_DEBUG_SEL3_R {
        LP_DEBUG_SEL3_R::new(((self.bits >> 21) & 0x7f) as u8)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("DEBUG_SEL0")
            .field("lp_debug_sel0", &self.lp_debug_sel0())
            .field("lp_debug_sel1", &self.lp_debug_sel1())
            .field("lp_debug_sel2", &self.lp_debug_sel2())
            .field("lp_debug_sel3", &self.lp_debug_sel3())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:6 - need des"]
    #[inline(always)]
    pub fn lp_debug_sel0(&mut self) -> LP_DEBUG_SEL0_W<'_, DEBUG_SEL0_SPEC> {
        LP_DEBUG_SEL0_W::new(self, 0)
    }
    #[doc = "Bits 7:13 - need des"]
    #[inline(always)]
    pub fn lp_debug_sel1(&mut self) -> LP_DEBUG_SEL1_W<'_, DEBUG_SEL0_SPEC> {
        LP_DEBUG_SEL1_W::new(self, 7)
    }
    #[doc = "Bits 14:20 - need des"]
    #[inline(always)]
    pub fn lp_debug_sel2(&mut self) -> LP_DEBUG_SEL2_W<'_, DEBUG_SEL0_SPEC> {
        LP_DEBUG_SEL2_W::new(self, 14)
    }
    #[doc = "Bits 21:27 - need des"]
    #[inline(always)]
    pub fn lp_debug_sel3(&mut self) -> LP_DEBUG_SEL3_W<'_, DEBUG_SEL0_SPEC> {
        LP_DEBUG_SEL3_W::new(self, 21)
    }
}
#[doc = "need des\n\nYou can [`read`](crate::Reg::read) this register and get [`debug_sel0::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`debug_sel0::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct DEBUG_SEL0_SPEC;
impl crate::RegisterSpec for DEBUG_SEL0_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`debug_sel0::R`](R) reader structure"]
impl crate::Readable for DEBUG_SEL0_SPEC {}
#[doc = "`write(|w| ..)` method takes [`debug_sel0::W`](W) writer structure"]
impl crate::Writable for DEBUG_SEL0_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets DEBUG_SEL0 to value 0"]
impl crate::Resettable for DEBUG_SEL0_SPEC {}
