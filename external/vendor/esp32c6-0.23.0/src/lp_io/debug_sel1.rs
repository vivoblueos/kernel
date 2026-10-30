#[doc = "Register `DEBUG_SEL1` reader"]
pub type R = crate::R<DEBUG_SEL1_SPEC>;
#[doc = "Register `DEBUG_SEL1` writer"]
pub type W = crate::W<DEBUG_SEL1_SPEC>;
#[doc = "Field `LP_DEBUG_SEL4` reader - need des"]
pub type LP_DEBUG_SEL4_R = crate::FieldReader;
#[doc = "Field `LP_DEBUG_SEL4` writer - need des"]
pub type LP_DEBUG_SEL4_W<'a, REG> = crate::FieldWriter<'a, REG, 7>;
impl R {
    #[doc = "Bits 0:6 - need des"]
    #[inline(always)]
    pub fn lp_debug_sel4(&self) -> LP_DEBUG_SEL4_R {
        LP_DEBUG_SEL4_R::new((self.bits & 0x7f) as u8)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("DEBUG_SEL1")
            .field("lp_debug_sel4", &self.lp_debug_sel4())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:6 - need des"]
    #[inline(always)]
    pub fn lp_debug_sel4(&mut self) -> LP_DEBUG_SEL4_W<'_, DEBUG_SEL1_SPEC> {
        LP_DEBUG_SEL4_W::new(self, 0)
    }
}
#[doc = "need des\n\nYou can [`read`](crate::Reg::read) this register and get [`debug_sel1::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`debug_sel1::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct DEBUG_SEL1_SPEC;
impl crate::RegisterSpec for DEBUG_SEL1_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`debug_sel1::R`](R) reader structure"]
impl crate::Readable for DEBUG_SEL1_SPEC {}
#[doc = "`write(|w| ..)` method takes [`debug_sel1::W`](W) writer structure"]
impl crate::Writable for DEBUG_SEL1_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets DEBUG_SEL1 to value 0"]
impl crate::Resettable for DEBUG_SEL1_SPEC {}
