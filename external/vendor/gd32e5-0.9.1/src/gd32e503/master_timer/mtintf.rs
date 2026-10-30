#[doc = "Register `MTINTF` reader"]
pub type R = crate::R<MtintfSpec>;
#[doc = "Field `CMP0IF` reader - Compare 0 interrupt flag"]
pub type Cmp0ifR = crate::BitReader;
#[doc = "Field `CMP1IF` reader - Compare 1 interrupt flag"]
pub type Cmp1ifR = crate::BitReader;
#[doc = "Field `CMP2IF` reader - Compare 2 interrupt flag"]
pub type Cmp2ifR = crate::BitReader;
#[doc = "Field `CMP3IF` reader - Compare 3 interrupt flag"]
pub type Cmp3ifR = crate::BitReader;
#[doc = "Field `REPIF` reader - Repetition interrupt flag"]
pub type RepifR = crate::BitReader;
#[doc = "Field `SYNIIF` reader - Synchronization input interrupt flag"]
pub type SyniifR = crate::BitReader;
#[doc = "Field `UPIF` reader - Update interrupt flag"]
pub type UpifR = crate::BitReader;
impl R {
    #[doc = "Bit 0 - Compare 0 interrupt flag"]
    #[inline(always)]
    pub fn cmp0if(&self) -> Cmp0ifR {
        Cmp0ifR::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - Compare 1 interrupt flag"]
    #[inline(always)]
    pub fn cmp1if(&self) -> Cmp1ifR {
        Cmp1ifR::new(((self.bits >> 1) & 1) != 0)
    }
    #[doc = "Bit 2 - Compare 2 interrupt flag"]
    #[inline(always)]
    pub fn cmp2if(&self) -> Cmp2ifR {
        Cmp2ifR::new(((self.bits >> 2) & 1) != 0)
    }
    #[doc = "Bit 3 - Compare 3 interrupt flag"]
    #[inline(always)]
    pub fn cmp3if(&self) -> Cmp3ifR {
        Cmp3ifR::new(((self.bits >> 3) & 1) != 0)
    }
    #[doc = "Bit 4 - Repetition interrupt flag"]
    #[inline(always)]
    pub fn repif(&self) -> RepifR {
        RepifR::new(((self.bits >> 4) & 1) != 0)
    }
    #[doc = "Bit 5 - Synchronization input interrupt flag"]
    #[inline(always)]
    pub fn syniif(&self) -> SyniifR {
        SyniifR::new(((self.bits >> 5) & 1) != 0)
    }
    #[doc = "Bit 6 - Update interrupt flag"]
    #[inline(always)]
    pub fn upif(&self) -> UpifR {
        UpifR::new(((self.bits >> 6) & 1) != 0)
    }
}
#[doc = "SHRTIMER Master_TIMER interrupt flag register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`mtintf::R`](R).  See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct MtintfSpec;
impl crate::RegisterSpec for MtintfSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`mtintf::R`](R) reader structure"]
impl crate::Readable for MtintfSpec {}
#[doc = "`reset()` method sets MTINTF to value 0"]
impl crate::Resettable for MtintfSpec {
    const RESET_VALUE: u32 = 0;
}
