#[doc = "Register `CMP1_CS` reader"]
pub type R = crate::R<Cmp1CsSpec>;
#[doc = "Register `CMP1_CS` writer"]
pub type W = crate::W<Cmp1CsSpec>;
#[doc = "Field `CMP1EN` reader - Comparator 1 enable"]
pub type Cmp1enR = crate::BitReader;
#[doc = "Field `CMP1EN` writer - Comparator 1 enable"]
pub type Cmp1enW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `CMP1MSEL` reader - Comparator 1 input selection"]
pub type Cmp1mselR = crate::FieldReader;
#[doc = "Field `CMP1MSEL` writer - Comparator 1 input selection"]
pub type Cmp1mselW<'a, REG> = crate::FieldWriter<'a, REG, 3>;
#[doc = "Field `CMP1OSEL` reader - Comparator 1 output selection"]
pub type Cmp1oselR = crate::FieldReader;
#[doc = "Field `CMP1OSEL` writer - Comparator 1 output selection"]
pub type Cmp1oselW<'a, REG> = crate::FieldWriter<'a, REG, 4>;
#[doc = "Field `CMP1PL` reader - Polarity of comparator 1 output"]
pub type Cmp1plR = crate::BitReader;
#[doc = "Field `CMP1PL` writer - Polarity of comparator 1 output"]
pub type Cmp1plW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `CMP1BLK` reader - CMP1 output blanking source"]
pub type Cmp1blkR = crate::FieldReader;
#[doc = "Field `CMP1BLK` writer - CMP1 output blanking source"]
pub type Cmp1blkW<'a, REG> = crate::FieldWriter<'a, REG, 3>;
#[doc = "Field `CMP1MSEL_3` reader - CMP1_IM input selection"]
pub type Cmp1msel3R = crate::BitReader;
#[doc = "Field `CMP1MSEL_3` writer - CMP1_IM input selection"]
pub type Cmp1msel3W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `CMP1O` reader - CMP1 output"]
pub type Cmp1oR = crate::BitReader;
#[doc = "Field `CMP1LK` reader - Comparator 1 lock"]
pub type Cmp1lkR = crate::BitReader;
#[doc = "Field `CMP1LK` writer - Comparator 1 lock"]
pub type Cmp1lkW<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 0 - Comparator 1 enable"]
    #[inline(always)]
    pub fn cmp1en(&self) -> Cmp1enR {
        Cmp1enR::new((self.bits & 1) != 0)
    }
    #[doc = "Bits 4:6 - Comparator 1 input selection"]
    #[inline(always)]
    pub fn cmp1msel(&self) -> Cmp1mselR {
        Cmp1mselR::new(((self.bits >> 4) & 7) as u8)
    }
    #[doc = "Bits 10:13 - Comparator 1 output selection"]
    #[inline(always)]
    pub fn cmp1osel(&self) -> Cmp1oselR {
        Cmp1oselR::new(((self.bits >> 10) & 0x0f) as u8)
    }
    #[doc = "Bit 15 - Polarity of comparator 1 output"]
    #[inline(always)]
    pub fn cmp1pl(&self) -> Cmp1plR {
        Cmp1plR::new(((self.bits >> 15) & 1) != 0)
    }
    #[doc = "Bits 18:20 - CMP1 output blanking source"]
    #[inline(always)]
    pub fn cmp1blk(&self) -> Cmp1blkR {
        Cmp1blkR::new(((self.bits >> 18) & 7) as u8)
    }
    #[doc = "Bit 22 - CMP1_IM input selection"]
    #[inline(always)]
    pub fn cmp1msel_3(&self) -> Cmp1msel3R {
        Cmp1msel3R::new(((self.bits >> 22) & 1) != 0)
    }
    #[doc = "Bit 30 - CMP1 output"]
    #[inline(always)]
    pub fn cmp1o(&self) -> Cmp1oR {
        Cmp1oR::new(((self.bits >> 30) & 1) != 0)
    }
    #[doc = "Bit 31 - Comparator 1 lock"]
    #[inline(always)]
    pub fn cmp1lk(&self) -> Cmp1lkR {
        Cmp1lkR::new(((self.bits >> 31) & 1) != 0)
    }
}
impl W {
    #[doc = "Bit 0 - Comparator 1 enable"]
    #[inline(always)]
    #[must_use]
    pub fn cmp1en(&mut self) -> Cmp1enW<Cmp1CsSpec> {
        Cmp1enW::new(self, 0)
    }
    #[doc = "Bits 4:6 - Comparator 1 input selection"]
    #[inline(always)]
    #[must_use]
    pub fn cmp1msel(&mut self) -> Cmp1mselW<Cmp1CsSpec> {
        Cmp1mselW::new(self, 4)
    }
    #[doc = "Bits 10:13 - Comparator 1 output selection"]
    #[inline(always)]
    #[must_use]
    pub fn cmp1osel(&mut self) -> Cmp1oselW<Cmp1CsSpec> {
        Cmp1oselW::new(self, 10)
    }
    #[doc = "Bit 15 - Polarity of comparator 1 output"]
    #[inline(always)]
    #[must_use]
    pub fn cmp1pl(&mut self) -> Cmp1plW<Cmp1CsSpec> {
        Cmp1plW::new(self, 15)
    }
    #[doc = "Bits 18:20 - CMP1 output blanking source"]
    #[inline(always)]
    #[must_use]
    pub fn cmp1blk(&mut self) -> Cmp1blkW<Cmp1CsSpec> {
        Cmp1blkW::new(self, 18)
    }
    #[doc = "Bit 22 - CMP1_IM input selection"]
    #[inline(always)]
    #[must_use]
    pub fn cmp1msel_3(&mut self) -> Cmp1msel3W<Cmp1CsSpec> {
        Cmp1msel3W::new(self, 22)
    }
    #[doc = "Bit 31 - Comparator 1 lock"]
    #[inline(always)]
    #[must_use]
    pub fn cmp1lk(&mut self) -> Cmp1lkW<Cmp1CsSpec> {
        Cmp1lkW::new(self, 31)
    }
}
#[doc = "CMP1 control and status register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`cmp1_cs::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`cmp1_cs::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct Cmp1CsSpec;
impl crate::RegisterSpec for Cmp1CsSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`cmp1_cs::R`](R) reader structure"]
impl crate::Readable for Cmp1CsSpec {}
#[doc = "`write(|w| ..)` method takes [`cmp1_cs::W`](W) writer structure"]
impl crate::Writable for Cmp1CsSpec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets CMP1_CS to value 0"]
impl crate::Resettable for Cmp1CsSpec {
    const RESET_VALUE: u32 = 0;
}
