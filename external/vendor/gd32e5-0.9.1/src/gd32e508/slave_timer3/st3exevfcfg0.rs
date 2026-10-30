#[doc = "Register `ST3EXEVFCFG0` reader"]
pub type R = crate::R<St3exevfcfg0Spec>;
#[doc = "Register `ST3EXEVFCFG0` writer"]
pub type W = crate::W<St3exevfcfg0Spec>;
#[doc = "Field `EXEV0MEEN` reader - External event 0 memorized enable"]
pub type Exev0meenR = crate::BitReader;
#[doc = "Field `EXEV0MEEN` writer - External event 0 memorized enable"]
pub type Exev0meenW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `EXEV0FM` reader - External event 0 filter mode"]
pub type Exev0fmR = crate::FieldReader;
#[doc = "Field `EXEV0FM` writer - External event 0 filter mode"]
pub type Exev0fmW<'a, REG> = crate::FieldWriter<'a, REG, 4>;
#[doc = "Field `EXEV1MEEN` reader - External event 1 memorized enable"]
pub type Exev1meenR = crate::BitReader;
#[doc = "Field `EXEV1MEEN` writer - External event 1 memorized enable"]
pub type Exev1meenW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `EXEV1FM` reader - External event 1 filter mode"]
pub type Exev1fmR = crate::FieldReader;
#[doc = "Field `EXEV1FM` writer - External event 1 filter mode"]
pub type Exev1fmW<'a, REG> = crate::FieldWriter<'a, REG, 4>;
#[doc = "Field `EXEV2MEEN` reader - External event 2 memorized enable"]
pub type Exev2meenR = crate::BitReader;
#[doc = "Field `EXEV2MEEN` writer - External event 2 memorized enable"]
pub type Exev2meenW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `EXEV2FM` reader - External event 2 filter mode"]
pub type Exev2fmR = crate::FieldReader;
#[doc = "Field `EXEV2FM` writer - External event 2 filter mode"]
pub type Exev2fmW<'a, REG> = crate::FieldWriter<'a, REG, 4>;
#[doc = "Field `EXEV3MEEN` reader - External event 3 memorized enable"]
pub type Exev3meenR = crate::BitReader;
#[doc = "Field `EXEV3MEEN` writer - External event 3 memorized enable"]
pub type Exev3meenW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `EXEV3FM` reader - External event 3 filter mode"]
pub type Exev3fmR = crate::FieldReader;
#[doc = "Field `EXEV3FM` writer - External event 3 filter mode"]
pub type Exev3fmW<'a, REG> = crate::FieldWriter<'a, REG, 4>;
#[doc = "Field `EXEV4MEEN` reader - External event 4 memorized enable"]
pub type Exev4meenR = crate::BitReader;
#[doc = "Field `EXEV4MEEN` writer - External event 4 memorized enable"]
pub type Exev4meenW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `EXEV4FM` reader - External event 4 filter mode"]
pub type Exev4fmR = crate::FieldReader;
#[doc = "Field `EXEV4FM` writer - External event 4 filter mode"]
pub type Exev4fmW<'a, REG> = crate::FieldWriter<'a, REG, 4>;
impl R {
    #[doc = "Bit 0 - External event 0 memorized enable"]
    #[inline(always)]
    pub fn exev0meen(&self) -> Exev0meenR {
        Exev0meenR::new((self.bits & 1) != 0)
    }
    #[doc = "Bits 1:4 - External event 0 filter mode"]
    #[inline(always)]
    pub fn exev0fm(&self) -> Exev0fmR {
        Exev0fmR::new(((self.bits >> 1) & 0x0f) as u8)
    }
    #[doc = "Bit 6 - External event 1 memorized enable"]
    #[inline(always)]
    pub fn exev1meen(&self) -> Exev1meenR {
        Exev1meenR::new(((self.bits >> 6) & 1) != 0)
    }
    #[doc = "Bits 7:10 - External event 1 filter mode"]
    #[inline(always)]
    pub fn exev1fm(&self) -> Exev1fmR {
        Exev1fmR::new(((self.bits >> 7) & 0x0f) as u8)
    }
    #[doc = "Bit 12 - External event 2 memorized enable"]
    #[inline(always)]
    pub fn exev2meen(&self) -> Exev2meenR {
        Exev2meenR::new(((self.bits >> 12) & 1) != 0)
    }
    #[doc = "Bits 13:16 - External event 2 filter mode"]
    #[inline(always)]
    pub fn exev2fm(&self) -> Exev2fmR {
        Exev2fmR::new(((self.bits >> 13) & 0x0f) as u8)
    }
    #[doc = "Bit 18 - External event 3 memorized enable"]
    #[inline(always)]
    pub fn exev3meen(&self) -> Exev3meenR {
        Exev3meenR::new(((self.bits >> 18) & 1) != 0)
    }
    #[doc = "Bits 19:22 - External event 3 filter mode"]
    #[inline(always)]
    pub fn exev3fm(&self) -> Exev3fmR {
        Exev3fmR::new(((self.bits >> 19) & 0x0f) as u8)
    }
    #[doc = "Bit 24 - External event 4 memorized enable"]
    #[inline(always)]
    pub fn exev4meen(&self) -> Exev4meenR {
        Exev4meenR::new(((self.bits >> 24) & 1) != 0)
    }
    #[doc = "Bits 25:28 - External event 4 filter mode"]
    #[inline(always)]
    pub fn exev4fm(&self) -> Exev4fmR {
        Exev4fmR::new(((self.bits >> 25) & 0x0f) as u8)
    }
}
impl W {
    #[doc = "Bit 0 - External event 0 memorized enable"]
    #[inline(always)]
    #[must_use]
    pub fn exev0meen(&mut self) -> Exev0meenW<St3exevfcfg0Spec> {
        Exev0meenW::new(self, 0)
    }
    #[doc = "Bits 1:4 - External event 0 filter mode"]
    #[inline(always)]
    #[must_use]
    pub fn exev0fm(&mut self) -> Exev0fmW<St3exevfcfg0Spec> {
        Exev0fmW::new(self, 1)
    }
    #[doc = "Bit 6 - External event 1 memorized enable"]
    #[inline(always)]
    #[must_use]
    pub fn exev1meen(&mut self) -> Exev1meenW<St3exevfcfg0Spec> {
        Exev1meenW::new(self, 6)
    }
    #[doc = "Bits 7:10 - External event 1 filter mode"]
    #[inline(always)]
    #[must_use]
    pub fn exev1fm(&mut self) -> Exev1fmW<St3exevfcfg0Spec> {
        Exev1fmW::new(self, 7)
    }
    #[doc = "Bit 12 - External event 2 memorized enable"]
    #[inline(always)]
    #[must_use]
    pub fn exev2meen(&mut self) -> Exev2meenW<St3exevfcfg0Spec> {
        Exev2meenW::new(self, 12)
    }
    #[doc = "Bits 13:16 - External event 2 filter mode"]
    #[inline(always)]
    #[must_use]
    pub fn exev2fm(&mut self) -> Exev2fmW<St3exevfcfg0Spec> {
        Exev2fmW::new(self, 13)
    }
    #[doc = "Bit 18 - External event 3 memorized enable"]
    #[inline(always)]
    #[must_use]
    pub fn exev3meen(&mut self) -> Exev3meenW<St3exevfcfg0Spec> {
        Exev3meenW::new(self, 18)
    }
    #[doc = "Bits 19:22 - External event 3 filter mode"]
    #[inline(always)]
    #[must_use]
    pub fn exev3fm(&mut self) -> Exev3fmW<St3exevfcfg0Spec> {
        Exev3fmW::new(self, 19)
    }
    #[doc = "Bit 24 - External event 4 memorized enable"]
    #[inline(always)]
    #[must_use]
    pub fn exev4meen(&mut self) -> Exev4meenW<St3exevfcfg0Spec> {
        Exev4meenW::new(self, 24)
    }
    #[doc = "Bits 25:28 - External event 4 filter mode"]
    #[inline(always)]
    #[must_use]
    pub fn exev4fm(&mut self) -> Exev4fmW<St3exevfcfg0Spec> {
        Exev4fmW::new(self, 25)
    }
}
#[doc = "SHRTIMER Slave_TIMERx external event filter configuration register 0\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`st3exevfcfg0::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`st3exevfcfg0::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct St3exevfcfg0Spec;
impl crate::RegisterSpec for St3exevfcfg0Spec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`st3exevfcfg0::R`](R) reader structure"]
impl crate::Readable for St3exevfcfg0Spec {}
#[doc = "`write(|w| ..)` method takes [`st3exevfcfg0::W`](W) writer structure"]
impl crate::Writable for St3exevfcfg0Spec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets ST3EXEVFCFG0 to value 0"]
impl crate::Resettable for St3exevfcfg0Spec {
    const RESET_VALUE: u32 = 0;
}
