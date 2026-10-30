#[doc = "Register `CMP5_CS` reader"]
pub type R = crate::R<Cmp5CsSpec>;
#[doc = "Register `CMP5_CS` writer"]
pub type W = crate::W<Cmp5CsSpec>;
#[doc = "Field `CMP5EN` reader - Comparator 5 enable"]
pub type Cmp5enR = crate::BitReader;
#[doc = "Field `CMP5EN` writer - Comparator 5 enable"]
pub type Cmp5enW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `CMP5MSEL` reader - Comparator 5 input selection"]
pub type Cmp5mselR = crate::FieldReader;
#[doc = "Field `CMP5MSEL` writer - Comparator 5 input selection"]
pub type Cmp5mselW<'a, REG> = crate::FieldWriter<'a, REG, 3>;
#[doc = "Field `CMP5OSEL` reader - Comparator 5 output selection"]
pub type Cmp5oselR = crate::FieldReader;
#[doc = "Field `CMP5OSEL` writer - Comparator 5 output selection"]
pub type Cmp5oselW<'a, REG> = crate::FieldWriter<'a, REG, 4>;
#[doc = "Field `CMP5PL` reader - Polarity of comparator 5 output"]
pub type Cmp5plR = crate::BitReader;
#[doc = "Field `CMP5PL` writer - Polarity of comparator 5 output"]
pub type Cmp5plW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `CMP5BLK` reader - CMP5 output blanking source"]
pub type Cmp5blkR = crate::FieldReader;
#[doc = "Field `CMP5BLK` writer - CMP5 output blanking source"]
pub type Cmp5blkW<'a, REG> = crate::FieldWriter<'a, REG, 3>;
#[doc = "Field `CMP5MSEL_3` reader - CMP5_IM input selection"]
pub type Cmp5msel3R = crate::BitReader;
#[doc = "Field `CMP5MSEL_3` writer - CMP5_IM input selection"]
pub type Cmp5msel3W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `CMP5O` reader - CMP5 output"]
pub type Cmp5oR = crate::BitReader;
#[doc = "Field `CMP5LK` reader - Comparator 5 lock"]
pub type Cmp5lkR = crate::BitReader;
#[doc = "Field `CMP5LK` writer - Comparator 5 lock"]
pub type Cmp5lkW<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 0 - Comparator 5 enable"]
    #[inline(always)]
    pub fn cmp5en(&self) -> Cmp5enR {
        Cmp5enR::new((self.bits & 1) != 0)
    }
    #[doc = "Bits 4:6 - Comparator 5 input selection"]
    #[inline(always)]
    pub fn cmp5msel(&self) -> Cmp5mselR {
        Cmp5mselR::new(((self.bits >> 4) & 7) as u8)
    }
    #[doc = "Bits 10:13 - Comparator 5 output selection"]
    #[inline(always)]
    pub fn cmp5osel(&self) -> Cmp5oselR {
        Cmp5oselR::new(((self.bits >> 10) & 0x0f) as u8)
    }
    #[doc = "Bit 15 - Polarity of comparator 5 output"]
    #[inline(always)]
    pub fn cmp5pl(&self) -> Cmp5plR {
        Cmp5plR::new(((self.bits >> 15) & 1) != 0)
    }
    #[doc = "Bits 18:20 - CMP5 output blanking source"]
    #[inline(always)]
    pub fn cmp5blk(&self) -> Cmp5blkR {
        Cmp5blkR::new(((self.bits >> 18) & 7) as u8)
    }
    #[doc = "Bit 22 - CMP5_IM input selection"]
    #[inline(always)]
    pub fn cmp5msel_3(&self) -> Cmp5msel3R {
        Cmp5msel3R::new(((self.bits >> 22) & 1) != 0)
    }
    #[doc = "Bit 30 - CMP5 output"]
    #[inline(always)]
    pub fn cmp5o(&self) -> Cmp5oR {
        Cmp5oR::new(((self.bits >> 30) & 1) != 0)
    }
    #[doc = "Bit 31 - Comparator 5 lock"]
    #[inline(always)]
    pub fn cmp5lk(&self) -> Cmp5lkR {
        Cmp5lkR::new(((self.bits >> 31) & 1) != 0)
    }
}
impl W {
    #[doc = "Bit 0 - Comparator 5 enable"]
    #[inline(always)]
    #[must_use]
    pub fn cmp5en(&mut self) -> Cmp5enW<Cmp5CsSpec> {
        Cmp5enW::new(self, 0)
    }
    #[doc = "Bits 4:6 - Comparator 5 input selection"]
    #[inline(always)]
    #[must_use]
    pub fn cmp5msel(&mut self) -> Cmp5mselW<Cmp5CsSpec> {
        Cmp5mselW::new(self, 4)
    }
    #[doc = "Bits 10:13 - Comparator 5 output selection"]
    #[inline(always)]
    #[must_use]
    pub fn cmp5osel(&mut self) -> Cmp5oselW<Cmp5CsSpec> {
        Cmp5oselW::new(self, 10)
    }
    #[doc = "Bit 15 - Polarity of comparator 5 output"]
    #[inline(always)]
    #[must_use]
    pub fn cmp5pl(&mut self) -> Cmp5plW<Cmp5CsSpec> {
        Cmp5plW::new(self, 15)
    }
    #[doc = "Bits 18:20 - CMP5 output blanking source"]
    #[inline(always)]
    #[must_use]
    pub fn cmp5blk(&mut self) -> Cmp5blkW<Cmp5CsSpec> {
        Cmp5blkW::new(self, 18)
    }
    #[doc = "Bit 22 - CMP5_IM input selection"]
    #[inline(always)]
    #[must_use]
    pub fn cmp5msel_3(&mut self) -> Cmp5msel3W<Cmp5CsSpec> {
        Cmp5msel3W::new(self, 22)
    }
    #[doc = "Bit 31 - Comparator 5 lock"]
    #[inline(always)]
    #[must_use]
    pub fn cmp5lk(&mut self) -> Cmp5lkW<Cmp5CsSpec> {
        Cmp5lkW::new(self, 31)
    }
}
#[doc = "CMP5 control and status register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`cmp5_cs::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`cmp5_cs::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct Cmp5CsSpec;
impl crate::RegisterSpec for Cmp5CsSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`cmp5_cs::R`](R) reader structure"]
impl crate::Readable for Cmp5CsSpec {}
#[doc = "`write(|w| ..)` method takes [`cmp5_cs::W`](W) writer structure"]
impl crate::Writable for Cmp5CsSpec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets CMP5_CS to value 0"]
impl crate::Resettable for Cmp5CsSpec {
    const RESET_VALUE: u32 = 0;
}
