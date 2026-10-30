#[doc = "Register `CTL0` reader"]
pub type R = crate::R<Ctl0Spec>;
#[doc = "Register `CTL0` writer"]
pub type W = crate::W<Ctl0Spec>;
#[doc = "Auto-reload shadow enable"]
pub use crate::gd32e507::timer0::ctl0::Arse;
#[doc = "Field `ARSE` reader - Auto-reload shadow enable"]
pub use crate::gd32e507::timer0::ctl0::ArseR;
#[doc = "Field `ARSE` writer - Auto-reload shadow enable"]
pub use crate::gd32e507::timer0::ctl0::ArseW;
#[doc = "Counter enable"]
pub use crate::gd32e507::timer0::ctl0::Cen;
#[doc = "Field `CEN` reader - Counter enable"]
pub use crate::gd32e507::timer0::ctl0::CenR;
#[doc = "Field `CEN` writer - Counter enable"]
pub use crate::gd32e507::timer0::ctl0::CenW;
#[doc = "Clock division"]
pub use crate::gd32e507::timer0::ctl0::Ckdiv;
#[doc = "Field `CKDIV` reader - Clock division"]
pub use crate::gd32e507::timer0::ctl0::CkdivR;
#[doc = "Field `CKDIV` writer - Clock division"]
pub use crate::gd32e507::timer0::ctl0::CkdivW;
#[doc = "Update disable"]
pub use crate::gd32e507::timer0::ctl0::Updis;
#[doc = "Field `UPDIS` reader - Update disable"]
pub use crate::gd32e507::timer0::ctl0::UpdisR;
#[doc = "Field `UPDIS` writer - Update disable"]
pub use crate::gd32e507::timer0::ctl0::UpdisW;
#[doc = "Update source"]
pub use crate::gd32e507::timer0::ctl0::Ups;
#[doc = "Field `UPS` reader - Update source"]
pub use crate::gd32e507::timer0::ctl0::UpsR;
#[doc = "Field `UPS` writer - Update source"]
pub use crate::gd32e507::timer0::ctl0::UpsW;
impl R {
    #[doc = "Bit 0 - Counter enable"]
    #[inline(always)]
    pub fn cen(&self) -> CenR {
        CenR::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - Update disable"]
    #[inline(always)]
    pub fn updis(&self) -> UpdisR {
        UpdisR::new(((self.bits >> 1) & 1) != 0)
    }
    #[doc = "Bit 2 - Update source"]
    #[inline(always)]
    pub fn ups(&self) -> UpsR {
        UpsR::new(((self.bits >> 2) & 1) != 0)
    }
    #[doc = "Bit 7 - Auto-reload shadow enable"]
    #[inline(always)]
    pub fn arse(&self) -> ArseR {
        ArseR::new(((self.bits >> 7) & 1) != 0)
    }
    #[doc = "Bits 8:9 - Clock division"]
    #[inline(always)]
    pub fn ckdiv(&self) -> CkdivR {
        CkdivR::new(((self.bits >> 8) & 3) as u8)
    }
}
impl W {
    #[doc = "Bit 0 - Counter enable"]
    #[inline(always)]
    #[must_use]
    pub fn cen(&mut self) -> CenW<Ctl0Spec> {
        CenW::new(self, 0)
    }
    #[doc = "Bit 1 - Update disable"]
    #[inline(always)]
    #[must_use]
    pub fn updis(&mut self) -> UpdisW<Ctl0Spec> {
        UpdisW::new(self, 1)
    }
    #[doc = "Bit 2 - Update source"]
    #[inline(always)]
    #[must_use]
    pub fn ups(&mut self) -> UpsW<Ctl0Spec> {
        UpsW::new(self, 2)
    }
    #[doc = "Bit 7 - Auto-reload shadow enable"]
    #[inline(always)]
    #[must_use]
    pub fn arse(&mut self) -> ArseW<Ctl0Spec> {
        ArseW::new(self, 7)
    }
    #[doc = "Bits 8:9 - Clock division"]
    #[inline(always)]
    #[must_use]
    pub fn ckdiv(&mut self) -> CkdivW<Ctl0Spec> {
        CkdivW::new(self, 8)
    }
}
#[doc = "control register 0\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`ctl0::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`ctl0::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct Ctl0Spec;
impl crate::RegisterSpec for Ctl0Spec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`ctl0::R`](R) reader structure"]
impl crate::Readable for Ctl0Spec {}
#[doc = "`write(|w| ..)` method takes [`ctl0::W`](W) writer structure"]
impl crate::Writable for Ctl0Spec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets CTL0 to value 0"]
impl crate::Resettable for Ctl0Spec {
    const RESET_VALUE: u32 = 0;
}
