#[doc = "Register `ADDAPB1RST` reader"]
pub type R = crate::R<Addapb1rstSpec>;
#[doc = "Register `ADDAPB1RST` writer"]
pub type W = crate::W<Addapb1rstSpec>;
#[doc = "Field `CTCRST` reader - CTC reset"]
pub type CtcrstR = crate::BitReader;
#[doc = "Field `CTCRST` writer - CTC reset"]
pub type CtcrstW<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 27 - CTC reset"]
    #[inline(always)]
    pub fn ctcrst(&self) -> CtcrstR {
        CtcrstR::new(((self.bits >> 27) & 1) != 0)
    }
}
impl W {
    #[doc = "Bit 27 - CTC reset"]
    #[inline(always)]
    #[must_use]
    pub fn ctcrst(&mut self) -> CtcrstW<Addapb1rstSpec> {
        CtcrstW::new(self, 27)
    }
}
#[doc = "APB1 additional reset register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`addapb1rst::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`addapb1rst::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct Addapb1rstSpec;
impl crate::RegisterSpec for Addapb1rstSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`addapb1rst::R`](R) reader structure"]
impl crate::Readable for Addapb1rstSpec {}
#[doc = "`write(|w| ..)` method takes [`addapb1rst::W`](W) writer structure"]
impl crate::Writable for Addapb1rstSpec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets ADDAPB1RST to value 0"]
impl crate::Resettable for Addapb1rstSpec {
    const RESET_VALUE: u32 = 0;
}
