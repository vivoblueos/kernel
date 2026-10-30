#[doc = "Register `ST2INTC` writer"]
pub type W = crate::W<St2intcSpec>;
#[doc = "Field `CMP0IFC` writer - Clear compare 0 interrupt flag"]
pub type Cmp0ifcW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `CMP1IFC` writer - Clear compare 1 interrupt flag"]
pub type Cmp1ifcW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `CMP2IFC` writer - Clear compare 2 interrupt flag"]
pub type Cmp2ifcW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `CMP3IFC` writer - Clear compare 3 interrupt flag"]
pub type Cmp3ifcW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `REPIFC` writer - Clear repetition interrupt flag"]
pub type RepifcW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `UPIFC` writer - Clear update interrupt flag"]
pub type UpifcW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `CAP0IFC` writer - Clear capture 0 interrupt flag"]
pub type Cap0ifcW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `CAP1IFC` writer - Clear capture 1 interrupt flag"]
pub type Cap1ifcW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `CH0OAIFC` writer - Clear channel 0 output active interrupt flag"]
pub type Ch0oaifcW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `CH0ONAIFC` writer - Clear channel 0 output inactive interrupt flag"]
pub type Ch0onaifcW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `CH1OAIFC` writer - Clear channel 1 output active interrupt flag"]
pub type Ch1oaifcW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `CH1ONAIFC` writer - Clear channel 1 output inactive interrupt flag"]
pub type Ch1onaifcW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `RSTIFC` writer - Clear counter reset interrupt flag"]
pub type RstifcW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `DLYIIFC` writer - Clear delayed IDLE mode entry interrupt flag"]
pub type DlyiifcW<'a, REG> = crate::BitWriter<'a, REG>;
impl W {
    #[doc = "Bit 0 - Clear compare 0 interrupt flag"]
    #[inline(always)]
    #[must_use]
    pub fn cmp0ifc(&mut self) -> Cmp0ifcW<St2intcSpec> {
        Cmp0ifcW::new(self, 0)
    }
    #[doc = "Bit 1 - Clear compare 1 interrupt flag"]
    #[inline(always)]
    #[must_use]
    pub fn cmp1ifc(&mut self) -> Cmp1ifcW<St2intcSpec> {
        Cmp1ifcW::new(self, 1)
    }
    #[doc = "Bit 2 - Clear compare 2 interrupt flag"]
    #[inline(always)]
    #[must_use]
    pub fn cmp2ifc(&mut self) -> Cmp2ifcW<St2intcSpec> {
        Cmp2ifcW::new(self, 2)
    }
    #[doc = "Bit 3 - Clear compare 3 interrupt flag"]
    #[inline(always)]
    #[must_use]
    pub fn cmp3ifc(&mut self) -> Cmp3ifcW<St2intcSpec> {
        Cmp3ifcW::new(self, 3)
    }
    #[doc = "Bit 4 - Clear repetition interrupt flag"]
    #[inline(always)]
    #[must_use]
    pub fn repifc(&mut self) -> RepifcW<St2intcSpec> {
        RepifcW::new(self, 4)
    }
    #[doc = "Bit 6 - Clear update interrupt flag"]
    #[inline(always)]
    #[must_use]
    pub fn upifc(&mut self) -> UpifcW<St2intcSpec> {
        UpifcW::new(self, 6)
    }
    #[doc = "Bit 7 - Clear capture 0 interrupt flag"]
    #[inline(always)]
    #[must_use]
    pub fn cap0ifc(&mut self) -> Cap0ifcW<St2intcSpec> {
        Cap0ifcW::new(self, 7)
    }
    #[doc = "Bit 8 - Clear capture 1 interrupt flag"]
    #[inline(always)]
    #[must_use]
    pub fn cap1ifc(&mut self) -> Cap1ifcW<St2intcSpec> {
        Cap1ifcW::new(self, 8)
    }
    #[doc = "Bit 9 - Clear channel 0 output active interrupt flag"]
    #[inline(always)]
    #[must_use]
    pub fn ch0oaifc(&mut self) -> Ch0oaifcW<St2intcSpec> {
        Ch0oaifcW::new(self, 9)
    }
    #[doc = "Bit 10 - Clear channel 0 output inactive interrupt flag"]
    #[inline(always)]
    #[must_use]
    pub fn ch0onaifc(&mut self) -> Ch0onaifcW<St2intcSpec> {
        Ch0onaifcW::new(self, 10)
    }
    #[doc = "Bit 11 - Clear channel 1 output active interrupt flag"]
    #[inline(always)]
    #[must_use]
    pub fn ch1oaifc(&mut self) -> Ch1oaifcW<St2intcSpec> {
        Ch1oaifcW::new(self, 11)
    }
    #[doc = "Bit 12 - Clear channel 1 output inactive interrupt flag"]
    #[inline(always)]
    #[must_use]
    pub fn ch1onaifc(&mut self) -> Ch1onaifcW<St2intcSpec> {
        Ch1onaifcW::new(self, 12)
    }
    #[doc = "Bit 13 - Clear counter reset interrupt flag"]
    #[inline(always)]
    #[must_use]
    pub fn rstifc(&mut self) -> RstifcW<St2intcSpec> {
        RstifcW::new(self, 13)
    }
    #[doc = "Bit 14 - Clear delayed IDLE mode entry interrupt flag"]
    #[inline(always)]
    #[must_use]
    pub fn dlyiifc(&mut self) -> DlyiifcW<St2intcSpec> {
        DlyiifcW::new(self, 14)
    }
}
#[doc = "SHRTIMER Slave_TIMERx interrupt flag clear register\n\nYou can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`st2intc::W`](W). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct St2intcSpec;
impl crate::RegisterSpec for St2intcSpec {
    type Ux = u32;
}
#[doc = "`write(|w| ..)` method takes [`st2intc::W`](W) writer structure"]
impl crate::Writable for St2intcSpec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets ST2INTC to value 0"]
impl crate::Resettable for St2intcSpec {
    const RESET_VALUE: u32 = 0;
}
