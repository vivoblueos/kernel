#[doc = "Register `CTL1` reader"]
pub type R = crate::R<Ctl1Spec>;
#[doc = "Register `CTL1` writer"]
pub type W = crate::W<Ctl1Spec>;
#[doc = "Field `CCSE` reader - Commutation control shadow enable"]
pub type CcseR = crate::BitReader;
#[doc = "Field `CCSE` writer - Commutation control shadow enable"]
pub type CcseW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `CCUC` reader - Commutation control shadow register update control"]
pub type CcucR = crate::BitReader;
#[doc = "Field `CCUC` writer - Commutation control shadow register update control"]
pub type CcucW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "DMA request source selection\n\nValue on reset: 0"]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Dmas {
    #[doc = "0: CCx DMA request sent when CCx event occurs"]
    OnCompare = 0,
    #[doc = "1: CCx DMA request sent when update event occurs"]
    OnUpdate = 1,
}
impl From<Dmas> for bool {
    #[inline(always)]
    fn from(variant: Dmas) -> Self {
        variant as u8 != 0
    }
}
#[doc = "Field `DMAS` reader - DMA request source selection"]
pub type DmasR = crate::BitReader<Dmas>;
impl DmasR {
    #[doc = "Get enumerated values variant"]
    #[inline(always)]
    pub const fn variant(&self) -> Dmas {
        match self.bits {
            false => Dmas::OnCompare,
            true => Dmas::OnUpdate,
        }
    }
    #[doc = "CCx DMA request sent when CCx event occurs"]
    #[inline(always)]
    pub fn is_on_compare(&self) -> bool {
        *self == Dmas::OnCompare
    }
    #[doc = "CCx DMA request sent when update event occurs"]
    #[inline(always)]
    pub fn is_on_update(&self) -> bool {
        *self == Dmas::OnUpdate
    }
}
#[doc = "Field `DMAS` writer - DMA request source selection"]
pub type DmasW<'a, REG> = crate::BitWriter<'a, REG, Dmas>;
impl<'a, REG> DmasW<'a, REG>
where
    REG: crate::Writable + crate::RegisterSpec,
{
    #[doc = "CCx DMA request sent when CCx event occurs"]
    #[inline(always)]
    pub fn on_compare(self) -> &'a mut crate::W<REG> {
        self.variant(Dmas::OnCompare)
    }
    #[doc = "CCx DMA request sent when update event occurs"]
    #[inline(always)]
    pub fn on_update(self) -> &'a mut crate::W<REG> {
        self.variant(Dmas::OnUpdate)
    }
}
#[doc = "Field `MMC` reader - Master mode control"]
pub type MmcR = crate::FieldReader;
#[doc = "Field `MMC` writer - Master mode control"]
pub type MmcW<'a, REG> = crate::FieldWriter<'a, REG, 3>;
#[doc = "Field `TI0S` reader - Channel 0 trigger input selection"]
pub type Ti0sR = crate::BitReader;
#[doc = "Field `TI0S` writer - Channel 0 trigger input selection"]
pub type Ti0sW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ISO0` reader - Idle state of channel 0 output"]
pub type Iso0R = crate::BitReader;
#[doc = "Field `ISO0` writer - Idle state of channel 0 output"]
pub type Iso0W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ISO0N` reader - Idle state of channel 0 complementary output"]
pub type Iso0nR = crate::BitReader;
#[doc = "Field `ISO0N` writer - Idle state of channel 0 complementary output"]
pub type Iso0nW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ISO1` reader - Idle state of channel 1 output"]
pub type Iso1R = crate::BitReader;
#[doc = "Field `ISO1` writer - Idle state of channel 1 output"]
pub type Iso1W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ISO1N` reader - Idle state of channel 1 complementary output"]
pub type Iso1nR = crate::BitReader;
#[doc = "Field `ISO1N` writer - Idle state of channel 1 complementary output"]
pub type Iso1nW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ISO2` reader - Idle state of channel 2 output"]
pub type Iso2R = crate::BitReader;
#[doc = "Field `ISO2` writer - Idle state of channel 2 output"]
pub type Iso2W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ISO2N` reader - Idle state of channel 2 complementary output"]
pub type Iso2nR = crate::BitReader;
#[doc = "Field `ISO2N` writer - Idle state of channel 2 complementary output"]
pub type Iso2nW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ISO3` reader - Idle state of channel 3 output"]
pub type Iso3R = crate::BitReader;
#[doc = "Field `ISO3` writer - Idle state of channel 3 output"]
pub type Iso3W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 0 - Commutation control shadow enable"]
    #[inline(always)]
    pub fn ccse(&self) -> CcseR {
        CcseR::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 2 - Commutation control shadow register update control"]
    #[inline(always)]
    pub fn ccuc(&self) -> CcucR {
        CcucR::new(((self.bits >> 2) & 1) != 0)
    }
    #[doc = "Bit 3 - DMA request source selection"]
    #[inline(always)]
    pub fn dmas(&self) -> DmasR {
        DmasR::new(((self.bits >> 3) & 1) != 0)
    }
    #[doc = "Bits 4:6 - Master mode control"]
    #[inline(always)]
    pub fn mmc(&self) -> MmcR {
        MmcR::new(((self.bits >> 4) & 7) as u8)
    }
    #[doc = "Bit 7 - Channel 0 trigger input selection"]
    #[inline(always)]
    pub fn ti0s(&self) -> Ti0sR {
        Ti0sR::new(((self.bits >> 7) & 1) != 0)
    }
    #[doc = "Bit 8 - Idle state of channel 0 output"]
    #[inline(always)]
    pub fn iso0(&self) -> Iso0R {
        Iso0R::new(((self.bits >> 8) & 1) != 0)
    }
    #[doc = "Bit 9 - Idle state of channel 0 complementary output"]
    #[inline(always)]
    pub fn iso0n(&self) -> Iso0nR {
        Iso0nR::new(((self.bits >> 9) & 1) != 0)
    }
    #[doc = "Bit 10 - Idle state of channel 1 output"]
    #[inline(always)]
    pub fn iso1(&self) -> Iso1R {
        Iso1R::new(((self.bits >> 10) & 1) != 0)
    }
    #[doc = "Bit 11 - Idle state of channel 1 complementary output"]
    #[inline(always)]
    pub fn iso1n(&self) -> Iso1nR {
        Iso1nR::new(((self.bits >> 11) & 1) != 0)
    }
    #[doc = "Bit 12 - Idle state of channel 2 output"]
    #[inline(always)]
    pub fn iso2(&self) -> Iso2R {
        Iso2R::new(((self.bits >> 12) & 1) != 0)
    }
    #[doc = "Bit 13 - Idle state of channel 2 complementary output"]
    #[inline(always)]
    pub fn iso2n(&self) -> Iso2nR {
        Iso2nR::new(((self.bits >> 13) & 1) != 0)
    }
    #[doc = "Bit 14 - Idle state of channel 3 output"]
    #[inline(always)]
    pub fn iso3(&self) -> Iso3R {
        Iso3R::new(((self.bits >> 14) & 1) != 0)
    }
}
impl W {
    #[doc = "Bit 0 - Commutation control shadow enable"]
    #[inline(always)]
    #[must_use]
    pub fn ccse(&mut self) -> CcseW<Ctl1Spec> {
        CcseW::new(self, 0)
    }
    #[doc = "Bit 2 - Commutation control shadow register update control"]
    #[inline(always)]
    #[must_use]
    pub fn ccuc(&mut self) -> CcucW<Ctl1Spec> {
        CcucW::new(self, 2)
    }
    #[doc = "Bit 3 - DMA request source selection"]
    #[inline(always)]
    #[must_use]
    pub fn dmas(&mut self) -> DmasW<Ctl1Spec> {
        DmasW::new(self, 3)
    }
    #[doc = "Bits 4:6 - Master mode control"]
    #[inline(always)]
    #[must_use]
    pub fn mmc(&mut self) -> MmcW<Ctl1Spec> {
        MmcW::new(self, 4)
    }
    #[doc = "Bit 7 - Channel 0 trigger input selection"]
    #[inline(always)]
    #[must_use]
    pub fn ti0s(&mut self) -> Ti0sW<Ctl1Spec> {
        Ti0sW::new(self, 7)
    }
    #[doc = "Bit 8 - Idle state of channel 0 output"]
    #[inline(always)]
    #[must_use]
    pub fn iso0(&mut self) -> Iso0W<Ctl1Spec> {
        Iso0W::new(self, 8)
    }
    #[doc = "Bit 9 - Idle state of channel 0 complementary output"]
    #[inline(always)]
    #[must_use]
    pub fn iso0n(&mut self) -> Iso0nW<Ctl1Spec> {
        Iso0nW::new(self, 9)
    }
    #[doc = "Bit 10 - Idle state of channel 1 output"]
    #[inline(always)]
    #[must_use]
    pub fn iso1(&mut self) -> Iso1W<Ctl1Spec> {
        Iso1W::new(self, 10)
    }
    #[doc = "Bit 11 - Idle state of channel 1 complementary output"]
    #[inline(always)]
    #[must_use]
    pub fn iso1n(&mut self) -> Iso1nW<Ctl1Spec> {
        Iso1nW::new(self, 11)
    }
    #[doc = "Bit 12 - Idle state of channel 2 output"]
    #[inline(always)]
    #[must_use]
    pub fn iso2(&mut self) -> Iso2W<Ctl1Spec> {
        Iso2W::new(self, 12)
    }
    #[doc = "Bit 13 - Idle state of channel 2 complementary output"]
    #[inline(always)]
    #[must_use]
    pub fn iso2n(&mut self) -> Iso2nW<Ctl1Spec> {
        Iso2nW::new(self, 13)
    }
    #[doc = "Bit 14 - Idle state of channel 3 output"]
    #[inline(always)]
    #[must_use]
    pub fn iso3(&mut self) -> Iso3W<Ctl1Spec> {
        Iso3W::new(self, 14)
    }
}
#[doc = "control register 1\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`ctl1::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`ctl1::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct Ctl1Spec;
impl crate::RegisterSpec for Ctl1Spec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`ctl1::R`](R) reader structure"]
impl crate::Readable for Ctl1Spec {}
#[doc = "`write(|w| ..)` method takes [`ctl1::W`](W) writer structure"]
impl crate::Writable for Ctl1Spec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets CTL1 to value 0"]
impl crate::Resettable for Ctl1Spec {
    const RESET_VALUE: u32 = 0;
}
