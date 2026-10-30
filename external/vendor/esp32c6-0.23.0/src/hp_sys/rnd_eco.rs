#[doc = "Register `RND_ECO` reader"]
pub type R = crate::R<RND_ECO_SPEC>;
#[doc = "Register `RND_ECO` writer"]
pub type W = crate::W<RND_ECO_SPEC>;
#[doc = "Field `REDCY_ENA` reader - Only reserved for ECO."]
pub type REDCY_ENA_R = crate::BitReader;
#[doc = "Field `REDCY_ENA` writer - Only reserved for ECO."]
pub type REDCY_ENA_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `REDCY_RESULT` reader - Only reserved for ECO."]
pub type REDCY_RESULT_R = crate::BitReader;
impl R {
    #[doc = "Bit 0 - Only reserved for ECO."]
    #[inline(always)]
    pub fn redcy_ena(&self) -> REDCY_ENA_R {
        REDCY_ENA_R::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - Only reserved for ECO."]
    #[inline(always)]
    pub fn redcy_result(&self) -> REDCY_RESULT_R {
        REDCY_RESULT_R::new(((self.bits >> 1) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("RND_ECO")
            .field("redcy_ena", &self.redcy_ena())
            .field("redcy_result", &self.redcy_result())
            .finish()
    }
}
impl W {
    #[doc = "Bit 0 - Only reserved for ECO."]
    #[inline(always)]
    pub fn redcy_ena(&mut self) -> REDCY_ENA_W<'_, RND_ECO_SPEC> {
        REDCY_ENA_W::new(self, 0)
    }
}
#[doc = "redcy eco register.\n\nYou can [`read`](crate::Reg::read) this register and get [`rnd_eco::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`rnd_eco::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct RND_ECO_SPEC;
impl crate::RegisterSpec for RND_ECO_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`rnd_eco::R`](R) reader structure"]
impl crate::Readable for RND_ECO_SPEC {}
#[doc = "`write(|w| ..)` method takes [`rnd_eco::W`](W) writer structure"]
impl crate::Writable for RND_ECO_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets RND_ECO to value 0"]
impl crate::Resettable for RND_ECO_SPEC {}
