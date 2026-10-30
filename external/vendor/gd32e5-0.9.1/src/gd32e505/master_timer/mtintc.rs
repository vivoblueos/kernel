#[doc = "Register `MTINTC` writer"]
pub type W = crate::W<MtintcSpec>;
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
#[doc = "Field `SYNIIFC` writer - Clear synchronization input interrupt flag"]
pub type SyniifcW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `UPIFC` writer - Clear update interrupt flag"]
pub type UpifcW<'a, REG> = crate::BitWriter<'a, REG>;
impl W {
    #[doc = "Bit 0 - Clear compare 0 interrupt flag"]
    #[inline(always)]
    #[must_use]
    pub fn cmp0ifc(&mut self) -> Cmp0ifcW<MtintcSpec> {
        Cmp0ifcW::new(self, 0)
    }
    #[doc = "Bit 1 - Clear compare 1 interrupt flag"]
    #[inline(always)]
    #[must_use]
    pub fn cmp1ifc(&mut self) -> Cmp1ifcW<MtintcSpec> {
        Cmp1ifcW::new(self, 1)
    }
    #[doc = "Bit 2 - Clear compare 2 interrupt flag"]
    #[inline(always)]
    #[must_use]
    pub fn cmp2ifc(&mut self) -> Cmp2ifcW<MtintcSpec> {
        Cmp2ifcW::new(self, 2)
    }
    #[doc = "Bit 3 - Clear compare 3 interrupt flag"]
    #[inline(always)]
    #[must_use]
    pub fn cmp3ifc(&mut self) -> Cmp3ifcW<MtintcSpec> {
        Cmp3ifcW::new(self, 3)
    }
    #[doc = "Bit 4 - Clear repetition interrupt flag"]
    #[inline(always)]
    #[must_use]
    pub fn repifc(&mut self) -> RepifcW<MtintcSpec> {
        RepifcW::new(self, 4)
    }
    #[doc = "Bit 5 - Clear synchronization input interrupt flag"]
    #[inline(always)]
    #[must_use]
    pub fn syniifc(&mut self) -> SyniifcW<MtintcSpec> {
        SyniifcW::new(self, 5)
    }
    #[doc = "Bit 6 - Clear update interrupt flag"]
    #[inline(always)]
    #[must_use]
    pub fn upifc(&mut self) -> UpifcW<MtintcSpec> {
        UpifcW::new(self, 6)
    }
}
#[doc = "SHRTIMER Master_TIMER interrupt flag clear register\n\nYou can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`mtintc::W`](W). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct MtintcSpec;
impl crate::RegisterSpec for MtintcSpec {
    type Ux = u32;
}
#[doc = "`write(|w| ..)` method takes [`mtintc::W`](W) writer structure"]
impl crate::Writable for MtintcSpec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets MTINTC to value 0"]
impl crate::Resettable for MtintcSpec {
    const RESET_VALUE: u32 = 0;
}
