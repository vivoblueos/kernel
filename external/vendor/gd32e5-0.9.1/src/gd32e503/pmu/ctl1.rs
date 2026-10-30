#[doc = "Register `CTL1` reader"]
pub type R = crate::R<Ctl1Spec>;
#[doc = "Register `CTL1` writer"]
pub type W = crate::W<Ctl1Spec>;
#[doc = "Field `DPMOD1` reader - Enable deep-sleep 1 mode"]
pub type Dpmod1R = crate::BitReader;
#[doc = "Field `DPMOD1` writer - Enable deep-sleep 1 mode"]
pub type Dpmod1W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `DPMOD2` reader - Enable deep-sleep 2 mode"]
pub type Dpmod2R = crate::BitReader;
#[doc = "Field `DPMOD2` writer - Enable deep-sleep 2 mode"]
pub type Dpmod2W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 0 - Enable deep-sleep 1 mode"]
    #[inline(always)]
    pub fn dpmod1(&self) -> Dpmod1R {
        Dpmod1R::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - Enable deep-sleep 2 mode"]
    #[inline(always)]
    pub fn dpmod2(&self) -> Dpmod2R {
        Dpmod2R::new(((self.bits >> 1) & 1) != 0)
    }
}
impl W {
    #[doc = "Bit 0 - Enable deep-sleep 1 mode"]
    #[inline(always)]
    #[must_use]
    pub fn dpmod1(&mut self) -> Dpmod1W<Ctl1Spec> {
        Dpmod1W::new(self, 0)
    }
    #[doc = "Bit 1 - Enable deep-sleep 2 mode"]
    #[inline(always)]
    #[must_use]
    pub fn dpmod2(&mut self) -> Dpmod2W<Ctl1Spec> {
        Dpmod2W::new(self, 1)
    }
}
#[doc = "power control register 1\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`ctl1::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`ctl1::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct Ctl1Spec;
impl crate::RegisterSpec for Ctl1Spec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`ctl1::R`](R) reader structure"]
impl crate::Readable for Ctl1Spec {}
#[doc = "`write(|w| ..)` method takes [`ctl1::W`](W) writer structure"]
impl crate::Writable for Ctl1Spec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets CTL1 to value 0"]
impl crate::Resettable for Ctl1Spec {
    const RESET_VALUE: u32 = 0;
}
