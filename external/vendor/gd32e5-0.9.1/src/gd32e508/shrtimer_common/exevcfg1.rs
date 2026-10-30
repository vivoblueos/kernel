#[doc = "Register `EXEVCFG1` reader"]
pub type R = crate::R<Exevcfg1Spec>;
#[doc = "Register `EXEVCFG1` writer"]
pub type W = crate::W<Exevcfg1Spec>;
#[doc = "Field `EXEV5SRC` reader - External event 0 source"]
pub type Exev5srcR = crate::FieldReader;
#[doc = "Field `EXEV5SRC` writer - External event 0 source"]
pub type Exev5srcW<'a, REG> = crate::FieldWriter<'a, REG, 2>;
#[doc = "Field `EXEV5P` reader - External event 0 polarity"]
pub type Exev5pR = crate::BitReader;
#[doc = "Field `EXEV5P` writer - External event 0 polarity"]
pub type Exev5pW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `EXEV5EG` reader - External event 0 edge sensitivity"]
pub type Exev5egR = crate::FieldReader;
#[doc = "Field `EXEV5EG` writer - External event 0 edge sensitivity"]
pub type Exev5egW<'a, REG> = crate::FieldWriter<'a, REG, 2>;
#[doc = "Field `EXEV6SRC` reader - External event 1 source"]
pub type Exev6srcR = crate::FieldReader;
#[doc = "Field `EXEV6SRC` writer - External event 1 source"]
pub type Exev6srcW<'a, REG> = crate::FieldWriter<'a, REG, 2>;
#[doc = "Field `EXEV6P` reader - External event 1 polarity"]
pub type Exev6pR = crate::BitReader;
#[doc = "Field `EXEV6P` writer - External event 1 polarity"]
pub type Exev6pW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `EXEV6EG` reader - External event 6 edge sensitivity"]
pub type Exev6egR = crate::FieldReader;
#[doc = "Field `EXEV6EG` writer - External event 6 edge sensitivity"]
pub type Exev6egW<'a, REG> = crate::FieldWriter<'a, REG, 2>;
#[doc = "Field `EXEV7SRC` reader - External event 7 source"]
pub type Exev7srcR = crate::FieldReader;
#[doc = "Field `EXEV7SRC` writer - External event 7 source"]
pub type Exev7srcW<'a, REG> = crate::FieldWriter<'a, REG, 2>;
#[doc = "Field `EXEV7P` reader - External event 7polarity"]
pub type Exev7pR = crate::BitReader;
#[doc = "Field `EXEV7P` writer - External event 7polarity"]
pub type Exev7pW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `EXEV7EG` reader - External event 7 edge sensitivity"]
pub type Exev7egR = crate::FieldReader;
#[doc = "Field `EXEV7EG` writer - External event 7 edge sensitivity"]
pub type Exev7egW<'a, REG> = crate::FieldWriter<'a, REG, 2>;
#[doc = "Field `EXEV8SRC` reader - External event 8 source"]
pub type Exev8srcR = crate::FieldReader;
#[doc = "Field `EXEV8SRC` writer - External event 8 source"]
pub type Exev8srcW<'a, REG> = crate::FieldWriter<'a, REG, 2>;
#[doc = "Field `EXEV8P` reader - External event 8 polarity"]
pub type Exev8pR = crate::BitReader;
#[doc = "Field `EXEV8P` writer - External event 8 polarity"]
pub type Exev8pW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `EXEV8EG` reader - External event 8 edge sensitivity"]
pub type Exev8egR = crate::FieldReader;
#[doc = "Field `EXEV8EG` writer - External event 8 edge sensitivity"]
pub type Exev8egW<'a, REG> = crate::FieldWriter<'a, REG, 2>;
#[doc = "Field `EXEV9SRC` reader - External event 9 source"]
pub type Exev9srcR = crate::FieldReader;
#[doc = "Field `EXEV9SRC` writer - External event 9 source"]
pub type Exev9srcW<'a, REG> = crate::FieldWriter<'a, REG, 2>;
#[doc = "Field `EXEV9P` reader - External event 9 polarity"]
pub type Exev9pR = crate::BitReader;
#[doc = "Field `EXEV9P` writer - External event 9 polarity"]
pub type Exev9pW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `EXEV9EG` reader - External event 9 edge sensitivity"]
pub type Exev9egR = crate::FieldReader;
#[doc = "Field `EXEV9EG` writer - External event 9 edge sensitivity"]
pub type Exev9egW<'a, REG> = crate::FieldWriter<'a, REG, 2>;
impl R {
    #[doc = "Bits 0:1 - External event 0 source"]
    #[inline(always)]
    pub fn exev5src(&self) -> Exev5srcR {
        Exev5srcR::new((self.bits & 3) as u8)
    }
    #[doc = "Bit 2 - External event 0 polarity"]
    #[inline(always)]
    pub fn exev5p(&self) -> Exev5pR {
        Exev5pR::new(((self.bits >> 2) & 1) != 0)
    }
    #[doc = "Bits 3:4 - External event 0 edge sensitivity"]
    #[inline(always)]
    pub fn exev5eg(&self) -> Exev5egR {
        Exev5egR::new(((self.bits >> 3) & 3) as u8)
    }
    #[doc = "Bits 6:7 - External event 1 source"]
    #[inline(always)]
    pub fn exev6src(&self) -> Exev6srcR {
        Exev6srcR::new(((self.bits >> 6) & 3) as u8)
    }
    #[doc = "Bit 8 - External event 1 polarity"]
    #[inline(always)]
    pub fn exev6p(&self) -> Exev6pR {
        Exev6pR::new(((self.bits >> 8) & 1) != 0)
    }
    #[doc = "Bits 9:10 - External event 6 edge sensitivity"]
    #[inline(always)]
    pub fn exev6eg(&self) -> Exev6egR {
        Exev6egR::new(((self.bits >> 9) & 3) as u8)
    }
    #[doc = "Bits 12:13 - External event 7 source"]
    #[inline(always)]
    pub fn exev7src(&self) -> Exev7srcR {
        Exev7srcR::new(((self.bits >> 12) & 3) as u8)
    }
    #[doc = "Bit 14 - External event 7polarity"]
    #[inline(always)]
    pub fn exev7p(&self) -> Exev7pR {
        Exev7pR::new(((self.bits >> 14) & 1) != 0)
    }
    #[doc = "Bits 15:16 - External event 7 edge sensitivity"]
    #[inline(always)]
    pub fn exev7eg(&self) -> Exev7egR {
        Exev7egR::new(((self.bits >> 15) & 3) as u8)
    }
    #[doc = "Bits 18:19 - External event 8 source"]
    #[inline(always)]
    pub fn exev8src(&self) -> Exev8srcR {
        Exev8srcR::new(((self.bits >> 18) & 3) as u8)
    }
    #[doc = "Bit 20 - External event 8 polarity"]
    #[inline(always)]
    pub fn exev8p(&self) -> Exev8pR {
        Exev8pR::new(((self.bits >> 20) & 1) != 0)
    }
    #[doc = "Bits 21:22 - External event 8 edge sensitivity"]
    #[inline(always)]
    pub fn exev8eg(&self) -> Exev8egR {
        Exev8egR::new(((self.bits >> 21) & 3) as u8)
    }
    #[doc = "Bits 24:25 - External event 9 source"]
    #[inline(always)]
    pub fn exev9src(&self) -> Exev9srcR {
        Exev9srcR::new(((self.bits >> 24) & 3) as u8)
    }
    #[doc = "Bit 26 - External event 9 polarity"]
    #[inline(always)]
    pub fn exev9p(&self) -> Exev9pR {
        Exev9pR::new(((self.bits >> 26) & 1) != 0)
    }
    #[doc = "Bits 27:28 - External event 9 edge sensitivity"]
    #[inline(always)]
    pub fn exev9eg(&self) -> Exev9egR {
        Exev9egR::new(((self.bits >> 27) & 3) as u8)
    }
}
impl W {
    #[doc = "Bits 0:1 - External event 0 source"]
    #[inline(always)]
    #[must_use]
    pub fn exev5src(&mut self) -> Exev5srcW<Exevcfg1Spec> {
        Exev5srcW::new(self, 0)
    }
    #[doc = "Bit 2 - External event 0 polarity"]
    #[inline(always)]
    #[must_use]
    pub fn exev5p(&mut self) -> Exev5pW<Exevcfg1Spec> {
        Exev5pW::new(self, 2)
    }
    #[doc = "Bits 3:4 - External event 0 edge sensitivity"]
    #[inline(always)]
    #[must_use]
    pub fn exev5eg(&mut self) -> Exev5egW<Exevcfg1Spec> {
        Exev5egW::new(self, 3)
    }
    #[doc = "Bits 6:7 - External event 1 source"]
    #[inline(always)]
    #[must_use]
    pub fn exev6src(&mut self) -> Exev6srcW<Exevcfg1Spec> {
        Exev6srcW::new(self, 6)
    }
    #[doc = "Bit 8 - External event 1 polarity"]
    #[inline(always)]
    #[must_use]
    pub fn exev6p(&mut self) -> Exev6pW<Exevcfg1Spec> {
        Exev6pW::new(self, 8)
    }
    #[doc = "Bits 9:10 - External event 6 edge sensitivity"]
    #[inline(always)]
    #[must_use]
    pub fn exev6eg(&mut self) -> Exev6egW<Exevcfg1Spec> {
        Exev6egW::new(self, 9)
    }
    #[doc = "Bits 12:13 - External event 7 source"]
    #[inline(always)]
    #[must_use]
    pub fn exev7src(&mut self) -> Exev7srcW<Exevcfg1Spec> {
        Exev7srcW::new(self, 12)
    }
    #[doc = "Bit 14 - External event 7polarity"]
    #[inline(always)]
    #[must_use]
    pub fn exev7p(&mut self) -> Exev7pW<Exevcfg1Spec> {
        Exev7pW::new(self, 14)
    }
    #[doc = "Bits 15:16 - External event 7 edge sensitivity"]
    #[inline(always)]
    #[must_use]
    pub fn exev7eg(&mut self) -> Exev7egW<Exevcfg1Spec> {
        Exev7egW::new(self, 15)
    }
    #[doc = "Bits 18:19 - External event 8 source"]
    #[inline(always)]
    #[must_use]
    pub fn exev8src(&mut self) -> Exev8srcW<Exevcfg1Spec> {
        Exev8srcW::new(self, 18)
    }
    #[doc = "Bit 20 - External event 8 polarity"]
    #[inline(always)]
    #[must_use]
    pub fn exev8p(&mut self) -> Exev8pW<Exevcfg1Spec> {
        Exev8pW::new(self, 20)
    }
    #[doc = "Bits 21:22 - External event 8 edge sensitivity"]
    #[inline(always)]
    #[must_use]
    pub fn exev8eg(&mut self) -> Exev8egW<Exevcfg1Spec> {
        Exev8egW::new(self, 21)
    }
    #[doc = "Bits 24:25 - External event 9 source"]
    #[inline(always)]
    #[must_use]
    pub fn exev9src(&mut self) -> Exev9srcW<Exevcfg1Spec> {
        Exev9srcW::new(self, 24)
    }
    #[doc = "Bit 26 - External event 9 polarity"]
    #[inline(always)]
    #[must_use]
    pub fn exev9p(&mut self) -> Exev9pW<Exevcfg1Spec> {
        Exev9pW::new(self, 26)
    }
    #[doc = "Bits 27:28 - External event 9 edge sensitivity"]
    #[inline(always)]
    #[must_use]
    pub fn exev9eg(&mut self) -> Exev9egW<Exevcfg1Spec> {
        Exev9egW::new(self, 27)
    }
}
#[doc = "SHRTIMER external event configuration register 1\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`exevcfg1::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`exevcfg1::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct Exevcfg1Spec;
impl crate::RegisterSpec for Exevcfg1Spec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`exevcfg1::R`](R) reader structure"]
impl crate::Readable for Exevcfg1Spec {}
#[doc = "`write(|w| ..)` method takes [`exevcfg1::W`](W) writer structure"]
impl crate::Writable for Exevcfg1Spec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets EXEVCFG1 to value 0"]
impl crate::Resettable for Exevcfg1Spec {
    const RESET_VALUE: u32 = 0;
}
