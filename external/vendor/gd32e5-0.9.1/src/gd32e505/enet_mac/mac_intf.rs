#[doc = "Register `MAC_INTF` reader"]
pub type R = crate::R<MacIntfSpec>;
#[doc = "Field `WUM` reader - WUM status"]
pub type WumR = crate::BitReader;
#[doc = "Field `MSC` reader - MSC status"]
pub type MscR = crate::BitReader;
#[doc = "Field `MSCR` reader - MSC receive status"]
pub type MscrR = crate::BitReader;
#[doc = "Field `MSCT` reader - MSC transmit status"]
pub type MsctR = crate::BitReader;
#[doc = "Field `TMST` reader - Time stamp trigger status"]
pub type TmstR = crate::BitReader;
impl R {
    #[doc = "Bit 3 - WUM status"]
    #[inline(always)]
    pub fn wum(&self) -> WumR {
        WumR::new(((self.bits >> 3) & 1) != 0)
    }
    #[doc = "Bit 4 - MSC status"]
    #[inline(always)]
    pub fn msc(&self) -> MscR {
        MscR::new(((self.bits >> 4) & 1) != 0)
    }
    #[doc = "Bit 5 - MSC receive status"]
    #[inline(always)]
    pub fn mscr(&self) -> MscrR {
        MscrR::new(((self.bits >> 5) & 1) != 0)
    }
    #[doc = "Bit 6 - MSC transmit status"]
    #[inline(always)]
    pub fn msct(&self) -> MsctR {
        MsctR::new(((self.bits >> 6) & 1) != 0)
    }
    #[doc = "Bit 9 - Time stamp trigger status"]
    #[inline(always)]
    pub fn tmst(&self) -> TmstR {
        TmstR::new(((self.bits >> 9) & 1) != 0)
    }
}
#[doc = "Ethernet MAC interrupt flag register (MAC_INTF)\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`mac_intf::R`](R).  See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct MacIntfSpec;
impl crate::RegisterSpec for MacIntfSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`mac_intf::R`](R) reader structure"]
impl crate::Readable for MacIntfSpec {}
#[doc = "`reset()` method sets MAC_INTF to value 0"]
impl crate::Resettable for MacIntfSpec {
    const RESET_VALUE: u32 = 0;
}
