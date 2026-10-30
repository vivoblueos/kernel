#[doc = "Register `STAT1` reader"]
pub type R = crate::R<Stat1Spec>;
#[doc = "Register `STAT1` writer"]
pub type W = crate::W<Stat1Spec>;
#[doc = "Field `RTF` writer - Receiver timeout flag"]
pub type RtfW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `EBF` writer - End of block flag"]
pub type EbfW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `BSY` reader - Busy flag"]
pub type BsyR = crate::BitReader;
impl R {
    #[doc = "Bit 16 - Busy flag"]
    #[inline(always)]
    pub fn bsy(&self) -> BsyR {
        BsyR::new(((self.bits >> 16) & 1) != 0)
    }
}
impl W {
    #[doc = "Bit 11 - Receiver timeout flag"]
    #[inline(always)]
    #[must_use]
    pub fn rtf(&mut self) -> RtfW<Stat1Spec> {
        RtfW::new(self, 11)
    }
    #[doc = "Bit 12 - End of block flag"]
    #[inline(always)]
    #[must_use]
    pub fn ebf(&mut self) -> EbfW<Stat1Spec> {
        EbfW::new(self, 12)
    }
}
#[doc = "Status register 1\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`stat1::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`stat1::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct Stat1Spec;
impl crate::RegisterSpec for Stat1Spec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`stat1::R`](R) reader structure"]
impl crate::Readable for Stat1Spec {}
#[doc = "`write(|w| ..)` method takes [`stat1::W`](W) writer structure"]
impl crate::Writable for Stat1Spec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets STAT1 to value 0"]
impl crate::Resettable for Stat1Spec {
    const RESET_VALUE: u32 = 0;
}
