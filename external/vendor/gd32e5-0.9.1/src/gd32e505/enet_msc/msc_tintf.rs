#[doc = "Register `MSC_TINTF` reader"]
pub type R = crate::R<MscTintfSpec>;
#[doc = "Field `TGFSC` reader - Transmitted good frames single collision"]
pub type TgfscR = crate::BitReader;
#[doc = "Field `TGFMSC` reader - Transmitted good frames more single collision"]
pub type TgfmscR = crate::BitReader;
#[doc = "Field `TGF` reader - Transmitted good frames"]
pub type TgfR = crate::BitReader;
impl R {
    #[doc = "Bit 14 - Transmitted good frames single collision"]
    #[inline(always)]
    pub fn tgfsc(&self) -> TgfscR {
        TgfscR::new(((self.bits >> 14) & 1) != 0)
    }
    #[doc = "Bit 15 - Transmitted good frames more single collision"]
    #[inline(always)]
    pub fn tgfmsc(&self) -> TgfmscR {
        TgfmscR::new(((self.bits >> 15) & 1) != 0)
    }
    #[doc = "Bit 21 - Transmitted good frames"]
    #[inline(always)]
    pub fn tgf(&self) -> TgfR {
        TgfR::new(((self.bits >> 21) & 1) != 0)
    }
}
#[doc = "Ethernet MSC transmit interrupt flag register (MSC_TINTF)\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`msc_tintf::R`](R).  See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct MscTintfSpec;
impl crate::RegisterSpec for MscTintfSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`msc_tintf::R`](R) reader structure"]
impl crate::Readable for MscTintfSpec {}
#[doc = "`reset()` method sets MSC_TINTF to value 0"]
impl crate::Resettable for MscTintfSpec {
    const RESET_VALUE: u32 = 0;
}
