#[doc = "Register `MSC_TINTMSK` reader"]
pub type R = crate::R<MscTintmskSpec>;
#[doc = "Register `MSC_TINTMSK` writer"]
pub type W = crate::W<MscTintmskSpec>;
#[doc = "Field `TGFSCIM` reader - Transmitted good frames single collision interrupt mask"]
pub type TgfscimR = crate::BitReader;
#[doc = "Field `TGFSCIM` writer - Transmitted good frames single collision interrupt mask"]
pub type TgfscimW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `TGFMSCIM` reader - Transmitted good frames more single interrupt collision mask"]
pub type TgfmscimR = crate::BitReader;
#[doc = "Field `TGFMSCIM` writer - Transmitted good frames more single interrupt collision mask"]
pub type TgfmscimW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `TGFIM` reader - Transmitted good frames interrupt mask"]
pub type TgfimR = crate::BitReader;
#[doc = "Field `TGFIM` writer - Transmitted good frames interrupt mask"]
pub type TgfimW<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 14 - Transmitted good frames single collision interrupt mask"]
    #[inline(always)]
    pub fn tgfscim(&self) -> TgfscimR {
        TgfscimR::new(((self.bits >> 14) & 1) != 0)
    }
    #[doc = "Bit 15 - Transmitted good frames more single interrupt collision mask"]
    #[inline(always)]
    pub fn tgfmscim(&self) -> TgfmscimR {
        TgfmscimR::new(((self.bits >> 15) & 1) != 0)
    }
    #[doc = "Bit 21 - Transmitted good frames interrupt mask"]
    #[inline(always)]
    pub fn tgfim(&self) -> TgfimR {
        TgfimR::new(((self.bits >> 21) & 1) != 0)
    }
}
impl W {
    #[doc = "Bit 14 - Transmitted good frames single collision interrupt mask"]
    #[inline(always)]
    #[must_use]
    pub fn tgfscim(&mut self) -> TgfscimW<MscTintmskSpec> {
        TgfscimW::new(self, 14)
    }
    #[doc = "Bit 15 - Transmitted good frames more single interrupt collision mask"]
    #[inline(always)]
    #[must_use]
    pub fn tgfmscim(&mut self) -> TgfmscimW<MscTintmskSpec> {
        TgfmscimW::new(self, 15)
    }
    #[doc = "Bit 21 - Transmitted good frames interrupt mask"]
    #[inline(always)]
    #[must_use]
    pub fn tgfim(&mut self) -> TgfimW<MscTintmskSpec> {
        TgfimW::new(self, 21)
    }
}
#[doc = "Ethernet MSC transmit interrupt mask register (MSC_TINTMSK)\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`msc_tintmsk::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`msc_tintmsk::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct MscTintmskSpec;
impl crate::RegisterSpec for MscTintmskSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`msc_tintmsk::R`](R) reader structure"]
impl crate::Readable for MscTintmskSpec {}
#[doc = "`write(|w| ..)` method takes [`msc_tintmsk::W`](W) writer structure"]
impl crate::Writable for MscTintmskSpec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets MSC_TINTMSK to value 0"]
impl crate::Resettable for MscTintmskSpec {
    const RESET_VALUE: u32 = 0;
}
