#[doc = "Register `ST2INTF` reader"]
pub type R = crate::R<St2intfSpec>;
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
#[doc = "Field `UPIF` reader - Update interrupt flag"]
pub type UpifR = crate::BitReader;
#[doc = "Field `CAP0IF` reader - Capture 0 interrupt flag"]
pub type Cap0ifR = crate::BitReader;
#[doc = "Field `CAP1IF` reader - Capture 1 interrupt flag"]
pub type Cap1ifR = crate::BitReader;
#[doc = "Field `CH0OAIF` reader - Channel 0 output active interrupt flag"]
pub type Ch0oaifR = crate::BitReader;
#[doc = "Field `CH0ONAIF` reader - Channel 0 output inactive interrupt flag"]
pub type Ch0onaifR = crate::BitReader;
#[doc = "Field `CH1OAIF` reader - Channel 1 output active interrupt flag"]
pub type Ch1oaifR = crate::BitReader;
#[doc = "Field `CH1ONAIF` reader - Channel 1 output inactive interrupt flag"]
pub type Ch1onaifR = crate::BitReader;
#[doc = "Field `RSTIF` reader - Counter reset interrupt flag"]
pub type RstifR = crate::BitReader;
#[doc = "Field `DLYIIF` reader - Delayed IDLE mode entry interrupt flag"]
pub type DlyiifR = crate::BitReader;
#[doc = "Field `CBLNF` reader - Current balanced flag"]
pub type CblnfR = crate::BitReader;
#[doc = "Field `BLNIF` reader - Balanced IDLE flag"]
pub type BlnifR = crate::BitReader;
#[doc = "Field `CH0F` reader - Channel 0 output flag"]
pub type Ch0fR = crate::BitReader;
#[doc = "Field `CH1F` reader - Channel 1 output flag"]
pub type Ch1fR = crate::BitReader;
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
    #[doc = "Bit 6 - Update interrupt flag"]
    #[inline(always)]
    pub fn upif(&self) -> UpifR {
        UpifR::new(((self.bits >> 6) & 1) != 0)
    }
    #[doc = "Bit 7 - Capture 0 interrupt flag"]
    #[inline(always)]
    pub fn cap0if(&self) -> Cap0ifR {
        Cap0ifR::new(((self.bits >> 7) & 1) != 0)
    }
    #[doc = "Bit 8 - Capture 1 interrupt flag"]
    #[inline(always)]
    pub fn cap1if(&self) -> Cap1ifR {
        Cap1ifR::new(((self.bits >> 8) & 1) != 0)
    }
    #[doc = "Bit 9 - Channel 0 output active interrupt flag"]
    #[inline(always)]
    pub fn ch0oaif(&self) -> Ch0oaifR {
        Ch0oaifR::new(((self.bits >> 9) & 1) != 0)
    }
    #[doc = "Bit 10 - Channel 0 output inactive interrupt flag"]
    #[inline(always)]
    pub fn ch0onaif(&self) -> Ch0onaifR {
        Ch0onaifR::new(((self.bits >> 10) & 1) != 0)
    }
    #[doc = "Bit 11 - Channel 1 output active interrupt flag"]
    #[inline(always)]
    pub fn ch1oaif(&self) -> Ch1oaifR {
        Ch1oaifR::new(((self.bits >> 11) & 1) != 0)
    }
    #[doc = "Bit 12 - Channel 1 output inactive interrupt flag"]
    #[inline(always)]
    pub fn ch1onaif(&self) -> Ch1onaifR {
        Ch1onaifR::new(((self.bits >> 12) & 1) != 0)
    }
    #[doc = "Bit 13 - Counter reset interrupt flag"]
    #[inline(always)]
    pub fn rstif(&self) -> RstifR {
        RstifR::new(((self.bits >> 13) & 1) != 0)
    }
    #[doc = "Bit 14 - Delayed IDLE mode entry interrupt flag"]
    #[inline(always)]
    pub fn dlyiif(&self) -> DlyiifR {
        DlyiifR::new(((self.bits >> 14) & 1) != 0)
    }
    #[doc = "Bit 16 - Current balanced flag"]
    #[inline(always)]
    pub fn cblnf(&self) -> CblnfR {
        CblnfR::new(((self.bits >> 16) & 1) != 0)
    }
    #[doc = "Bit 17 - Balanced IDLE flag"]
    #[inline(always)]
    pub fn blnif(&self) -> BlnifR {
        BlnifR::new(((self.bits >> 17) & 1) != 0)
    }
    #[doc = "Bit 20 - Channel 0 output flag"]
    #[inline(always)]
    pub fn ch0f(&self) -> Ch0fR {
        Ch0fR::new(((self.bits >> 20) & 1) != 0)
    }
    #[doc = "Bit 21 - Channel 1 output flag"]
    #[inline(always)]
    pub fn ch1f(&self) -> Ch1fR {
        Ch1fR::new(((self.bits >> 21) & 1) != 0)
    }
}
#[doc = "SHRTIMER Slave_TIMERx interrupt flag register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`st2intf::R`](R).  See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct St2intfSpec;
impl crate::RegisterSpec for St2intfSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`st2intf::R`](R) reader structure"]
impl crate::Readable for St2intfSpec {}
#[doc = "`reset()` method sets ST2INTF to value 0"]
impl crate::Resettable for St2intfSpec {
    const RESET_VALUE: u32 = 0;
}
