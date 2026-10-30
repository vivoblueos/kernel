#[doc = "Register `FILTER_CTRL1` reader"]
pub type R = crate::R<FILTER_CTRL1_SPEC>;
#[doc = "Register `FILTER_CTRL1` writer"]
pub type W = crate::W<FILTER_CTRL1_SPEC>;
#[doc = "Field `FILTER_FACTOR1` reader - Factor of saradc filter1"]
pub type FILTER_FACTOR1_R = crate::FieldReader;
#[doc = "Field `FILTER_FACTOR1` writer - Factor of saradc filter1"]
pub type FILTER_FACTOR1_W<'a, REG> = crate::FieldWriter<'a, REG, 3>;
#[doc = "Field `FILTER_FACTOR0` reader - Factor of saradc filter0"]
pub type FILTER_FACTOR0_R = crate::FieldReader;
#[doc = "Field `FILTER_FACTOR0` writer - Factor of saradc filter0"]
pub type FILTER_FACTOR0_W<'a, REG> = crate::FieldWriter<'a, REG, 3>;
impl R {
    #[doc = "Bits 26:28 - Factor of saradc filter1"]
    #[inline(always)]
    pub fn filter_factor1(&self) -> FILTER_FACTOR1_R {
        FILTER_FACTOR1_R::new(((self.bits >> 26) & 7) as u8)
    }
    #[doc = "Bits 29:31 - Factor of saradc filter0"]
    #[inline(always)]
    pub fn filter_factor0(&self) -> FILTER_FACTOR0_R {
        FILTER_FACTOR0_R::new(((self.bits >> 29) & 7) as u8)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("FILTER_CTRL1")
            .field("filter_factor1", &self.filter_factor1())
            .field("filter_factor0", &self.filter_factor0())
            .finish()
    }
}
impl W {
    #[doc = "Bits 26:28 - Factor of saradc filter1"]
    #[inline(always)]
    pub fn filter_factor1(&mut self) -> FILTER_FACTOR1_W<'_, FILTER_CTRL1_SPEC> {
        FILTER_FACTOR1_W::new(self, 26)
    }
    #[doc = "Bits 29:31 - Factor of saradc filter0"]
    #[inline(always)]
    pub fn filter_factor0(&mut self) -> FILTER_FACTOR0_W<'_, FILTER_CTRL1_SPEC> {
        FILTER_FACTOR0_W::new(self, 29)
    }
}
#[doc = "digital saradc configure register\n\nYou can [`read`](crate::Reg::read) this register and get [`filter_ctrl1::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`filter_ctrl1::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct FILTER_CTRL1_SPEC;
impl crate::RegisterSpec for FILTER_CTRL1_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`filter_ctrl1::R`](R) reader structure"]
impl crate::Readable for FILTER_CTRL1_SPEC {}
#[doc = "`write(|w| ..)` method takes [`filter_ctrl1::W`](W) writer structure"]
impl crate::Writable for FILTER_CTRL1_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets FILTER_CTRL1 to value 0"]
impl crate::Resettable for FILTER_CTRL1_SPEC {}
