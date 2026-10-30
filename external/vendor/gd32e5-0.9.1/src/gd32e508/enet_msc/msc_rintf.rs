#[doc = "Register `MSC_RINTF` reader"]
pub type R = crate::R<MscRintfSpec>;
#[doc = "Field `RFCE` reader - Received frames CRC error"]
pub type RfceR = crate::BitReader;
#[doc = "Field `RFAE` reader - Received frames alignment error"]
pub type RfaeR = crate::BitReader;
#[doc = "Field `RGUF` reader - Received Good Unicast Frames"]
pub type RgufR = crate::BitReader;
impl R {
    #[doc = "Bit 5 - Received frames CRC error"]
    #[inline(always)]
    pub fn rfce(&self) -> RfceR {
        RfceR::new(((self.bits >> 5) & 1) != 0)
    }
    #[doc = "Bit 6 - Received frames alignment error"]
    #[inline(always)]
    pub fn rfae(&self) -> RfaeR {
        RfaeR::new(((self.bits >> 6) & 1) != 0)
    }
    #[doc = "Bit 17 - Received Good Unicast Frames"]
    #[inline(always)]
    pub fn rguf(&self) -> RgufR {
        RgufR::new(((self.bits >> 17) & 1) != 0)
    }
}
#[doc = "Ethernet MSC receive interrupt flag register (MSC_RINTF)\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`msc_rintf::R`](R).  See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct MscRintfSpec;
impl crate::RegisterSpec for MscRintfSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`msc_rintf::R`](R) reader structure"]
impl crate::Readable for MscRintfSpec {}
#[doc = "`reset()` method sets MSC_RINTF to value 0"]
impl crate::Resettable for MscRintfSpec {
    const RESET_VALUE: u32 = 0;
}
