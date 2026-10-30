#[doc = "Register `MTDMAINTEN` reader"]
pub type R = crate::R<MtdmaintenSpec>;
#[doc = "Register `MTDMAINTEN` writer"]
pub type W = crate::W<MtdmaintenSpec>;
#[doc = "Field `CMP0IE` reader - Compare 0 interrupt enable"]
pub type Cmp0ieR = crate::BitReader;
#[doc = "Field `CMP0IE` writer - Compare 0 interrupt enable"]
pub type Cmp0ieW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `CMP1IE` reader - Compare 1 interrupt enable"]
pub type Cmp1ieR = crate::BitReader;
#[doc = "Field `CMP1IE` writer - Compare 1 interrupt enable"]
pub type Cmp1ieW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `CMP2IE` reader - Compare 2 interrupt enable"]
pub type Cmp2ieR = crate::BitReader;
#[doc = "Field `CMP2IE` writer - Compare 2 interrupt enable"]
pub type Cmp2ieW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `CMP3IE` reader - Compare 3 interrupt enable"]
pub type Cmp3ieR = crate::BitReader;
#[doc = "Field `CMP3IE` writer - Compare 3 interrupt enable"]
pub type Cmp3ieW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `REPIE` reader - Repetition interrupt enable"]
pub type RepieR = crate::BitReader;
#[doc = "Field `REPIE` writer - Repetition interrupt enable"]
pub type RepieW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SYNIIE` reader - Synchronization input interrupt enable"]
pub type SyniieR = crate::BitReader;
#[doc = "Field `SYNIIE` writer - Synchronization input interrupt enable"]
pub type SyniieW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `UPIE` reader - Update interrupt enable"]
pub type UpieR = crate::BitReader;
#[doc = "Field `UPIE` writer - Update interrupt enable"]
pub type UpieW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `CMP0DEN` reader - Compare 0 DMA request enable"]
pub type Cmp0denR = crate::BitReader;
#[doc = "Field `CMP0DEN` writer - Compare 0 DMA request enable"]
pub type Cmp0denW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `CMP1DEN` reader - Compare 1 DMA request enable"]
pub type Cmp1denR = crate::BitReader;
#[doc = "Field `CMP1DEN` writer - Compare 1 DMA request enable"]
pub type Cmp1denW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `CMP2DEN` reader - Compare 2 DMA request enable"]
pub type Cmp2denR = crate::BitReader;
#[doc = "Field `CMP2DEN` writer - Compare 2 DMA request enable"]
pub type Cmp2denW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `CMP3DEN` reader - Compare 3 DMA request enable"]
pub type Cmp3denR = crate::BitReader;
#[doc = "Field `CMP3DEN` writer - Compare 3 DMA request enable"]
pub type Cmp3denW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `REPDEN` reader - Repetition DMA request enable"]
pub type RepdenR = crate::BitReader;
#[doc = "Field `REPDEN` writer - Repetition DMA request enable"]
pub type RepdenW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SYNIDEN` reader - Synchronization input DMA request enable"]
pub type SynidenR = crate::BitReader;
#[doc = "Field `SYNIDEN` writer - Synchronization input DMA request enable"]
pub type SynidenW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `UPDEN` reader - Update DMA request enable"]
pub type UpdenR = crate::BitReader;
#[doc = "Field `UPDEN` writer - Update DMA request enable"]
pub type UpdenW<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 0 - Compare 0 interrupt enable"]
    #[inline(always)]
    pub fn cmp0ie(&self) -> Cmp0ieR {
        Cmp0ieR::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - Compare 1 interrupt enable"]
    #[inline(always)]
    pub fn cmp1ie(&self) -> Cmp1ieR {
        Cmp1ieR::new(((self.bits >> 1) & 1) != 0)
    }
    #[doc = "Bit 2 - Compare 2 interrupt enable"]
    #[inline(always)]
    pub fn cmp2ie(&self) -> Cmp2ieR {
        Cmp2ieR::new(((self.bits >> 2) & 1) != 0)
    }
    #[doc = "Bit 3 - Compare 3 interrupt enable"]
    #[inline(always)]
    pub fn cmp3ie(&self) -> Cmp3ieR {
        Cmp3ieR::new(((self.bits >> 3) & 1) != 0)
    }
    #[doc = "Bit 4 - Repetition interrupt enable"]
    #[inline(always)]
    pub fn repie(&self) -> RepieR {
        RepieR::new(((self.bits >> 4) & 1) != 0)
    }
    #[doc = "Bit 5 - Synchronization input interrupt enable"]
    #[inline(always)]
    pub fn syniie(&self) -> SyniieR {
        SyniieR::new(((self.bits >> 5) & 1) != 0)
    }
    #[doc = "Bit 6 - Update interrupt enable"]
    #[inline(always)]
    pub fn upie(&self) -> UpieR {
        UpieR::new(((self.bits >> 6) & 1) != 0)
    }
    #[doc = "Bit 16 - Compare 0 DMA request enable"]
    #[inline(always)]
    pub fn cmp0den(&self) -> Cmp0denR {
        Cmp0denR::new(((self.bits >> 16) & 1) != 0)
    }
    #[doc = "Bit 17 - Compare 1 DMA request enable"]
    #[inline(always)]
    pub fn cmp1den(&self) -> Cmp1denR {
        Cmp1denR::new(((self.bits >> 17) & 1) != 0)
    }
    #[doc = "Bit 18 - Compare 2 DMA request enable"]
    #[inline(always)]
    pub fn cmp2den(&self) -> Cmp2denR {
        Cmp2denR::new(((self.bits >> 18) & 1) != 0)
    }
    #[doc = "Bit 19 - Compare 3 DMA request enable"]
    #[inline(always)]
    pub fn cmp3den(&self) -> Cmp3denR {
        Cmp3denR::new(((self.bits >> 19) & 1) != 0)
    }
    #[doc = "Bit 20 - Repetition DMA request enable"]
    #[inline(always)]
    pub fn repden(&self) -> RepdenR {
        RepdenR::new(((self.bits >> 20) & 1) != 0)
    }
    #[doc = "Bit 21 - Synchronization input DMA request enable"]
    #[inline(always)]
    pub fn syniden(&self) -> SynidenR {
        SynidenR::new(((self.bits >> 21) & 1) != 0)
    }
    #[doc = "Bit 22 - Update DMA request enable"]
    #[inline(always)]
    pub fn upden(&self) -> UpdenR {
        UpdenR::new(((self.bits >> 22) & 1) != 0)
    }
}
impl W {
    #[doc = "Bit 0 - Compare 0 interrupt enable"]
    #[inline(always)]
    #[must_use]
    pub fn cmp0ie(&mut self) -> Cmp0ieW<MtdmaintenSpec> {
        Cmp0ieW::new(self, 0)
    }
    #[doc = "Bit 1 - Compare 1 interrupt enable"]
    #[inline(always)]
    #[must_use]
    pub fn cmp1ie(&mut self) -> Cmp1ieW<MtdmaintenSpec> {
        Cmp1ieW::new(self, 1)
    }
    #[doc = "Bit 2 - Compare 2 interrupt enable"]
    #[inline(always)]
    #[must_use]
    pub fn cmp2ie(&mut self) -> Cmp2ieW<MtdmaintenSpec> {
        Cmp2ieW::new(self, 2)
    }
    #[doc = "Bit 3 - Compare 3 interrupt enable"]
    #[inline(always)]
    #[must_use]
    pub fn cmp3ie(&mut self) -> Cmp3ieW<MtdmaintenSpec> {
        Cmp3ieW::new(self, 3)
    }
    #[doc = "Bit 4 - Repetition interrupt enable"]
    #[inline(always)]
    #[must_use]
    pub fn repie(&mut self) -> RepieW<MtdmaintenSpec> {
        RepieW::new(self, 4)
    }
    #[doc = "Bit 5 - Synchronization input interrupt enable"]
    #[inline(always)]
    #[must_use]
    pub fn syniie(&mut self) -> SyniieW<MtdmaintenSpec> {
        SyniieW::new(self, 5)
    }
    #[doc = "Bit 6 - Update interrupt enable"]
    #[inline(always)]
    #[must_use]
    pub fn upie(&mut self) -> UpieW<MtdmaintenSpec> {
        UpieW::new(self, 6)
    }
    #[doc = "Bit 16 - Compare 0 DMA request enable"]
    #[inline(always)]
    #[must_use]
    pub fn cmp0den(&mut self) -> Cmp0denW<MtdmaintenSpec> {
        Cmp0denW::new(self, 16)
    }
    #[doc = "Bit 17 - Compare 1 DMA request enable"]
    #[inline(always)]
    #[must_use]
    pub fn cmp1den(&mut self) -> Cmp1denW<MtdmaintenSpec> {
        Cmp1denW::new(self, 17)
    }
    #[doc = "Bit 18 - Compare 2 DMA request enable"]
    #[inline(always)]
    #[must_use]
    pub fn cmp2den(&mut self) -> Cmp2denW<MtdmaintenSpec> {
        Cmp2denW::new(self, 18)
    }
    #[doc = "Bit 19 - Compare 3 DMA request enable"]
    #[inline(always)]
    #[must_use]
    pub fn cmp3den(&mut self) -> Cmp3denW<MtdmaintenSpec> {
        Cmp3denW::new(self, 19)
    }
    #[doc = "Bit 20 - Repetition DMA request enable"]
    #[inline(always)]
    #[must_use]
    pub fn repden(&mut self) -> RepdenW<MtdmaintenSpec> {
        RepdenW::new(self, 20)
    }
    #[doc = "Bit 21 - Synchronization input DMA request enable"]
    #[inline(always)]
    #[must_use]
    pub fn syniden(&mut self) -> SynidenW<MtdmaintenSpec> {
        SynidenW::new(self, 21)
    }
    #[doc = "Bit 22 - Update DMA request enable"]
    #[inline(always)]
    #[must_use]
    pub fn upden(&mut self) -> UpdenW<MtdmaintenSpec> {
        UpdenW::new(self, 22)
    }
}
#[doc = "SHRTIMER Master_TIMER DMA and interrupt enable register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`mtdmainten::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`mtdmainten::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct MtdmaintenSpec;
impl crate::RegisterSpec for MtdmaintenSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`mtdmainten::R`](R) reader structure"]
impl crate::Readable for MtdmaintenSpec {}
#[doc = "`write(|w| ..)` method takes [`mtdmainten::W`](W) writer structure"]
impl crate::Writable for MtdmaintenSpec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets MTDMAINTEN to value 0"]
impl crate::Resettable for MtdmaintenSpec {
    const RESET_VALUE: u32 = 0;
}
