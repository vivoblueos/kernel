#[doc = "Register `ADDAPB1EN` reader"]
pub type R = crate::R<Addapb1enSpec>;
#[doc = "Register `ADDAPB1EN` writer"]
pub type W = crate::W<Addapb1enSpec>;
#[doc = "Field `CTCEN` reader - CTC clock enable"]
pub type CtcenR = crate::BitReader;
#[doc = "Field `CTCEN` writer - CTC clock enable"]
pub type CtcenW<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 27 - CTC clock enable"]
    #[inline(always)]
    pub fn ctcen(&self) -> CtcenR {
        CtcenR::new(((self.bits >> 27) & 1) != 0)
    }
}
impl W {
    #[doc = "Bit 27 - CTC clock enable"]
    #[inline(always)]
    #[must_use]
    pub fn ctcen(&mut self) -> CtcenW<Addapb1enSpec> {
        CtcenW::new(self, 27)
    }
}
#[doc = "APB1 additional enable register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`addapb1en::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`addapb1en::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct Addapb1enSpec;
impl crate::RegisterSpec for Addapb1enSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`addapb1en::R`](R) reader structure"]
impl crate::Readable for Addapb1enSpec {}
#[doc = "`write(|w| ..)` method takes [`addapb1en::W`](W) writer structure"]
impl crate::Writable for Addapb1enSpec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets ADDAPB1EN to value 0"]
impl crate::Resettable for Addapb1enSpec {
    const RESET_VALUE: u32 = 0;
}
