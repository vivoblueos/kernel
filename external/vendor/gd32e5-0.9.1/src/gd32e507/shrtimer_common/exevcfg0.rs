#[doc = "Register `EXEVCFG0` reader"]
pub type R = crate::R<Exevcfg0Spec>;
#[doc = "Register `EXEVCFG0` writer"]
pub type W = crate::W<Exevcfg0Spec>;
#[doc = "Field `EXEV0SRC` reader - External event 0 source"]
pub type Exev0srcR = crate::FieldReader;
#[doc = "Field `EXEV0SRC` writer - External event 0 source"]
pub type Exev0srcW<'a, REG> = crate::FieldWriter<'a, REG, 2>;
#[doc = "Field `EXEV0P` reader - External event 0 polarity"]
pub type Exev0pR = crate::BitReader;
#[doc = "Field `EXEV0P` writer - External event 0 polarity"]
pub type Exev0pW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `EXEV0EG` reader - External event 0 edge sensitivity"]
pub type Exev0egR = crate::FieldReader;
#[doc = "Field `EXEV0EG` writer - External event 0 edge sensitivity"]
pub type Exev0egW<'a, REG> = crate::FieldWriter<'a, REG, 2>;
#[doc = "Field `EXEV1SRC` reader - External event 1 source"]
pub type Exev1srcR = crate::FieldReader;
#[doc = "Field `EXEV1SRC` writer - External event 1 source"]
pub type Exev1srcW<'a, REG> = crate::FieldWriter<'a, REG, 2>;
#[doc = "Field `EXEV1P` reader - External event 1 polarity"]
pub type Exev1pR = crate::BitReader;
#[doc = "Field `EXEV1P` writer - External event 1 polarity"]
pub type Exev1pW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `EXEV1EG` reader - External event 1 edge sensitivity"]
pub type Exev1egR = crate::FieldReader;
#[doc = "Field `EXEV1EG` writer - External event 1 edge sensitivity"]
pub type Exev1egW<'a, REG> = crate::FieldWriter<'a, REG, 2>;
#[doc = "Field `EXEV2SRC` reader - External event 2 source"]
pub type Exev2srcR = crate::FieldReader;
#[doc = "Field `EXEV2SRC` writer - External event 2 source"]
pub type Exev2srcW<'a, REG> = crate::FieldWriter<'a, REG, 2>;
#[doc = "Field `EXEV2P` reader - External event 2 polarity"]
pub type Exev2pR = crate::BitReader;
#[doc = "Field `EXEV2P` writer - External event 2 polarity"]
pub type Exev2pW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `EXEV2EG` reader - External event 2 edge sensitivity"]
pub type Exev2egR = crate::FieldReader;
#[doc = "Field `EXEV2EG` writer - External event 2 edge sensitivity"]
pub type Exev2egW<'a, REG> = crate::FieldWriter<'a, REG, 2>;
#[doc = "Field `EXEV3SRC` reader - External event 3 source"]
pub type Exev3srcR = crate::FieldReader;
#[doc = "Field `EXEV3SRC` writer - External event 3 source"]
pub type Exev3srcW<'a, REG> = crate::FieldWriter<'a, REG, 2>;
#[doc = "Field `EXEV3P` reader - External event 3 polarity"]
pub type Exev3pR = crate::BitReader;
#[doc = "Field `EXEV3P` writer - External event 3 polarity"]
pub type Exev3pW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `EXEV3EG` reader - External event 3 edge sensitivity"]
pub type Exev3egR = crate::FieldReader;
#[doc = "Field `EXEV3EG` writer - External event 3 edge sensitivity"]
pub type Exev3egW<'a, REG> = crate::FieldWriter<'a, REG, 2>;
#[doc = "Field `EXEV4SRC` reader - External event 4 source"]
pub type Exev4srcR = crate::FieldReader;
#[doc = "Field `EXEV4SRC` writer - External event 4 source"]
pub type Exev4srcW<'a, REG> = crate::FieldWriter<'a, REG, 2>;
#[doc = "Field `EXEV4P` reader - External event 4 polarity"]
pub type Exev4pR = crate::BitReader;
#[doc = "Field `EXEV4P` writer - External event 4 polarity"]
pub type Exev4pW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `EXEV4EG` reader - External event 4 edge sensitivity"]
pub type Exev4egR = crate::FieldReader;
#[doc = "Field `EXEV4EG` writer - External event 4 edge sensitivity"]
pub type Exev4egW<'a, REG> = crate::FieldWriter<'a, REG, 2>;
impl R {
    #[doc = "Bits 0:1 - External event 0 source"]
    #[inline(always)]
    pub fn exev0src(&self) -> Exev0srcR {
        Exev0srcR::new((self.bits & 3) as u8)
    }
    #[doc = "Bit 2 - External event 0 polarity"]
    #[inline(always)]
    pub fn exev0p(&self) -> Exev0pR {
        Exev0pR::new(((self.bits >> 2) & 1) != 0)
    }
    #[doc = "Bits 3:4 - External event 0 edge sensitivity"]
    #[inline(always)]
    pub fn exev0eg(&self) -> Exev0egR {
        Exev0egR::new(((self.bits >> 3) & 3) as u8)
    }
    #[doc = "Bits 6:7 - External event 1 source"]
    #[inline(always)]
    pub fn exev1src(&self) -> Exev1srcR {
        Exev1srcR::new(((self.bits >> 6) & 3) as u8)
    }
    #[doc = "Bit 8 - External event 1 polarity"]
    #[inline(always)]
    pub fn exev1p(&self) -> Exev1pR {
        Exev1pR::new(((self.bits >> 8) & 1) != 0)
    }
    #[doc = "Bits 9:10 - External event 1 edge sensitivity"]
    #[inline(always)]
    pub fn exev1eg(&self) -> Exev1egR {
        Exev1egR::new(((self.bits >> 9) & 3) as u8)
    }
    #[doc = "Bits 12:13 - External event 2 source"]
    #[inline(always)]
    pub fn exev2src(&self) -> Exev2srcR {
        Exev2srcR::new(((self.bits >> 12) & 3) as u8)
    }
    #[doc = "Bit 14 - External event 2 polarity"]
    #[inline(always)]
    pub fn exev2p(&self) -> Exev2pR {
        Exev2pR::new(((self.bits >> 14) & 1) != 0)
    }
    #[doc = "Bits 15:16 - External event 2 edge sensitivity"]
    #[inline(always)]
    pub fn exev2eg(&self) -> Exev2egR {
        Exev2egR::new(((self.bits >> 15) & 3) as u8)
    }
    #[doc = "Bits 18:19 - External event 3 source"]
    #[inline(always)]
    pub fn exev3src(&self) -> Exev3srcR {
        Exev3srcR::new(((self.bits >> 18) & 3) as u8)
    }
    #[doc = "Bit 20 - External event 3 polarity"]
    #[inline(always)]
    pub fn exev3p(&self) -> Exev3pR {
        Exev3pR::new(((self.bits >> 20) & 1) != 0)
    }
    #[doc = "Bits 21:22 - External event 3 edge sensitivity"]
    #[inline(always)]
    pub fn exev3eg(&self) -> Exev3egR {
        Exev3egR::new(((self.bits >> 21) & 3) as u8)
    }
    #[doc = "Bits 24:25 - External event 4 source"]
    #[inline(always)]
    pub fn exev4src(&self) -> Exev4srcR {
        Exev4srcR::new(((self.bits >> 24) & 3) as u8)
    }
    #[doc = "Bit 26 - External event 4 polarity"]
    #[inline(always)]
    pub fn exev4p(&self) -> Exev4pR {
        Exev4pR::new(((self.bits >> 26) & 1) != 0)
    }
    #[doc = "Bits 27:28 - External event 4 edge sensitivity"]
    #[inline(always)]
    pub fn exev4eg(&self) -> Exev4egR {
        Exev4egR::new(((self.bits >> 27) & 3) as u8)
    }
}
impl W {
    #[doc = "Bits 0:1 - External event 0 source"]
    #[inline(always)]
    #[must_use]
    pub fn exev0src(&mut self) -> Exev0srcW<Exevcfg0Spec> {
        Exev0srcW::new(self, 0)
    }
    #[doc = "Bit 2 - External event 0 polarity"]
    #[inline(always)]
    #[must_use]
    pub fn exev0p(&mut self) -> Exev0pW<Exevcfg0Spec> {
        Exev0pW::new(self, 2)
    }
    #[doc = "Bits 3:4 - External event 0 edge sensitivity"]
    #[inline(always)]
    #[must_use]
    pub fn exev0eg(&mut self) -> Exev0egW<Exevcfg0Spec> {
        Exev0egW::new(self, 3)
    }
    #[doc = "Bits 6:7 - External event 1 source"]
    #[inline(always)]
    #[must_use]
    pub fn exev1src(&mut self) -> Exev1srcW<Exevcfg0Spec> {
        Exev1srcW::new(self, 6)
    }
    #[doc = "Bit 8 - External event 1 polarity"]
    #[inline(always)]
    #[must_use]
    pub fn exev1p(&mut self) -> Exev1pW<Exevcfg0Spec> {
        Exev1pW::new(self, 8)
    }
    #[doc = "Bits 9:10 - External event 1 edge sensitivity"]
    #[inline(always)]
    #[must_use]
    pub fn exev1eg(&mut self) -> Exev1egW<Exevcfg0Spec> {
        Exev1egW::new(self, 9)
    }
    #[doc = "Bits 12:13 - External event 2 source"]
    #[inline(always)]
    #[must_use]
    pub fn exev2src(&mut self) -> Exev2srcW<Exevcfg0Spec> {
        Exev2srcW::new(self, 12)
    }
    #[doc = "Bit 14 - External event 2 polarity"]
    #[inline(always)]
    #[must_use]
    pub fn exev2p(&mut self) -> Exev2pW<Exevcfg0Spec> {
        Exev2pW::new(self, 14)
    }
    #[doc = "Bits 15:16 - External event 2 edge sensitivity"]
    #[inline(always)]
    #[must_use]
    pub fn exev2eg(&mut self) -> Exev2egW<Exevcfg0Spec> {
        Exev2egW::new(self, 15)
    }
    #[doc = "Bits 18:19 - External event 3 source"]
    #[inline(always)]
    #[must_use]
    pub fn exev3src(&mut self) -> Exev3srcW<Exevcfg0Spec> {
        Exev3srcW::new(self, 18)
    }
    #[doc = "Bit 20 - External event 3 polarity"]
    #[inline(always)]
    #[must_use]
    pub fn exev3p(&mut self) -> Exev3pW<Exevcfg0Spec> {
        Exev3pW::new(self, 20)
    }
    #[doc = "Bits 21:22 - External event 3 edge sensitivity"]
    #[inline(always)]
    #[must_use]
    pub fn exev3eg(&mut self) -> Exev3egW<Exevcfg0Spec> {
        Exev3egW::new(self, 21)
    }
    #[doc = "Bits 24:25 - External event 4 source"]
    #[inline(always)]
    #[must_use]
    pub fn exev4src(&mut self) -> Exev4srcW<Exevcfg0Spec> {
        Exev4srcW::new(self, 24)
    }
    #[doc = "Bit 26 - External event 4 polarity"]
    #[inline(always)]
    #[must_use]
    pub fn exev4p(&mut self) -> Exev4pW<Exevcfg0Spec> {
        Exev4pW::new(self, 26)
    }
    #[doc = "Bits 27:28 - External event 4 edge sensitivity"]
    #[inline(always)]
    #[must_use]
    pub fn exev4eg(&mut self) -> Exev4egW<Exevcfg0Spec> {
        Exev4egW::new(self, 27)
    }
}
#[doc = "SHRTIMER external event configuration register 0\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`exevcfg0::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`exevcfg0::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct Exevcfg0Spec;
impl crate::RegisterSpec for Exevcfg0Spec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`exevcfg0::R`](R) reader structure"]
impl crate::Readable for Exevcfg0Spec {}
#[doc = "`write(|w| ..)` method takes [`exevcfg0::W`](W) writer structure"]
impl crate::Writable for Exevcfg0Spec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets EXEVCFG0 to value 0"]
impl crate::Resettable for Exevcfg0Spec {
    const RESET_VALUE: u32 = 0;
}
