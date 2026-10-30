#[doc = "Register `CTL2` reader"]
pub type R = crate::R<Ctl2Spec>;
#[doc = "Register `CTL2` writer"]
pub type W = crate::W<Ctl2Spec>;
#[doc = "Field `FMPEN` reader - Fast mode plus enable"]
pub type FmpenR = crate::BitReader;
#[doc = "Field `FMPEN` writer - Fast mode plus enable"]
pub type FmpenW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SETM` reader - Start Early Termination Mode"]
pub type SetmR = crate::BitReader;
#[doc = "Field `SETM` writer - Start Early Termination Mode"]
pub type SetmW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `TOEN` reader - Timeout calculation enable"]
pub type ToenR = crate::BitReader;
#[doc = "Field `TOEN` writer - Timeout calculation enable"]
pub type ToenW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `RADD` reader - slave address recorde enable"]
pub type RaddR = crate::BitReader;
#[doc = "Field `RADD` writer - slave address recorde enable"]
pub type RaddW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ADDM` reader - ingnore specify bits"]
pub type AddmR = crate::FieldReader;
#[doc = "Field `ADDM` writer - ingnore specify bits"]
pub type AddmW<'a, REG> = crate::FieldWriter<'a, REG, 7>;
impl R {
    #[doc = "Bit 0 - Fast mode plus enable"]
    #[inline(always)]
    pub fn fmpen(&self) -> FmpenR {
        FmpenR::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - Start Early Termination Mode"]
    #[inline(always)]
    pub fn setm(&self) -> SetmR {
        SetmR::new(((self.bits >> 1) & 1) != 0)
    }
    #[doc = "Bit 4 - Timeout calculation enable"]
    #[inline(always)]
    pub fn toen(&self) -> ToenR {
        ToenR::new(((self.bits >> 4) & 1) != 0)
    }
    #[doc = "Bit 8 - slave address recorde enable"]
    #[inline(always)]
    pub fn radd(&self) -> RaddR {
        RaddR::new(((self.bits >> 8) & 1) != 0)
    }
    #[doc = "Bits 9:15 - ingnore specify bits"]
    #[inline(always)]
    pub fn addm(&self) -> AddmR {
        AddmR::new(((self.bits >> 9) & 0x7f) as u8)
    }
}
impl W {
    #[doc = "Bit 0 - Fast mode plus enable"]
    #[inline(always)]
    #[must_use]
    pub fn fmpen(&mut self) -> FmpenW<Ctl2Spec> {
        FmpenW::new(self, 0)
    }
    #[doc = "Bit 1 - Start Early Termination Mode"]
    #[inline(always)]
    #[must_use]
    pub fn setm(&mut self) -> SetmW<Ctl2Spec> {
        SetmW::new(self, 1)
    }
    #[doc = "Bit 4 - Timeout calculation enable"]
    #[inline(always)]
    #[must_use]
    pub fn toen(&mut self) -> ToenW<Ctl2Spec> {
        ToenW::new(self, 4)
    }
    #[doc = "Bit 8 - slave address recorde enable"]
    #[inline(always)]
    #[must_use]
    pub fn radd(&mut self) -> RaddW<Ctl2Spec> {
        RaddW::new(self, 8)
    }
    #[doc = "Bits 9:15 - ingnore specify bits"]
    #[inline(always)]
    #[must_use]
    pub fn addm(&mut self) -> AddmW<Ctl2Spec> {
        AddmW::new(self, 9)
    }
}
#[doc = "Control register 2\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`ctl2::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`ctl2::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct Ctl2Spec;
impl crate::RegisterSpec for Ctl2Spec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`ctl2::R`](R) reader structure"]
impl crate::Readable for Ctl2Spec {}
#[doc = "`write(|w| ..)` method takes [`ctl2::W`](W) writer structure"]
impl crate::Writable for Ctl2Spec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets CTL2 to value 0xfe00"]
impl crate::Resettable for Ctl2Spec {
    const RESET_VALUE: u32 = 0xfe00;
}
