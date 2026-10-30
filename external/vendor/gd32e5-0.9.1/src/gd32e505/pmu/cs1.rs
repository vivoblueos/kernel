#[doc = "Register `CS1` reader"]
pub type R = crate::R<Cs1Spec>;
#[doc = "Register `CS1` writer"]
pub type W = crate::W<Cs1Spec>;
#[doc = "Field `DPF1` reader - Deep-sleep1 mode status flag"]
pub type Dpf1R = crate::BitReader;
#[doc = "Field `DPF1` writer - Deep-sleep1 mode status flag"]
pub type Dpf1W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `DPF2` reader - Deep-sleep 2 mode status flag"]
pub type Dpf2R = crate::BitReader;
#[doc = "Field `DPF2` writer - Deep-sleep 2 mode status flag"]
pub type Dpf2W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 0 - Deep-sleep1 mode status flag"]
    #[inline(always)]
    pub fn dpf1(&self) -> Dpf1R {
        Dpf1R::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - Deep-sleep 2 mode status flag"]
    #[inline(always)]
    pub fn dpf2(&self) -> Dpf2R {
        Dpf2R::new(((self.bits >> 1) & 1) != 0)
    }
}
impl W {
    #[doc = "Bit 0 - Deep-sleep1 mode status flag"]
    #[inline(always)]
    #[must_use]
    pub fn dpf1(&mut self) -> Dpf1W<Cs1Spec> {
        Dpf1W::new(self, 0)
    }
    #[doc = "Bit 1 - Deep-sleep 2 mode status flag"]
    #[inline(always)]
    #[must_use]
    pub fn dpf2(&mut self) -> Dpf2W<Cs1Spec> {
        Dpf2W::new(self, 1)
    }
}
#[doc = "power control and status register 1\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`cs1::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`cs1::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct Cs1Spec;
impl crate::RegisterSpec for Cs1Spec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`cs1::R`](R) reader structure"]
impl crate::Readable for Cs1Spec {}
#[doc = "`write(|w| ..)` method takes [`cs1::W`](W) writer structure"]
impl crate::Writable for Cs1Spec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets CS1 to value 0"]
impl crate::Resettable for Cs1Spec {
    const RESET_VALUE: u32 = 0;
}
