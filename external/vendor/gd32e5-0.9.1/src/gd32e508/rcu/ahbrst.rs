#[doc = "Register `AHBRST` reader"]
pub type R = crate::R<AhbrstSpec>;
#[doc = "Register `AHBRST` writer"]
pub type W = crate::W<AhbrstSpec>;
#[doc = "Field `USBHSRST` reader - USBHS reset"]
pub type UsbhsrstR = crate::BitReader;
#[doc = "Field `USBHSRST` writer - USBHS reset"]
pub type UsbhsrstW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ENETRST` reader - ENET reset"]
pub type EnetrstR = crate::BitReader;
#[doc = "Field `ENETRST` writer - ENET reset"]
pub type EnetrstW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `TMURST` reader - TMU reset"]
pub type TmurstR = crate::BitReader;
#[doc = "Field `TMURST` writer - TMU reset"]
pub type TmurstW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SQPIRST` reader - SQPI reset"]
pub type SqpirstR = crate::BitReader;
#[doc = "Field `SQPIRST` writer - SQPI reset"]
pub type SqpirstW<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 12 - USBHS reset"]
    #[inline(always)]
    pub fn usbhsrst(&self) -> UsbhsrstR {
        UsbhsrstR::new(((self.bits >> 12) & 1) != 0)
    }
    #[doc = "Bit 14 - ENET reset"]
    #[inline(always)]
    pub fn enetrst(&self) -> EnetrstR {
        EnetrstR::new(((self.bits >> 14) & 1) != 0)
    }
    #[doc = "Bit 30 - TMU reset"]
    #[inline(always)]
    pub fn tmurst(&self) -> TmurstR {
        TmurstR::new(((self.bits >> 30) & 1) != 0)
    }
    #[doc = "Bit 31 - SQPI reset"]
    #[inline(always)]
    pub fn sqpirst(&self) -> SqpirstR {
        SqpirstR::new(((self.bits >> 31) & 1) != 0)
    }
}
impl W {
    #[doc = "Bit 12 - USBHS reset"]
    #[inline(always)]
    #[must_use]
    pub fn usbhsrst(&mut self) -> UsbhsrstW<AhbrstSpec> {
        UsbhsrstW::new(self, 12)
    }
    #[doc = "Bit 14 - ENET reset"]
    #[inline(always)]
    #[must_use]
    pub fn enetrst(&mut self) -> EnetrstW<AhbrstSpec> {
        EnetrstW::new(self, 14)
    }
    #[doc = "Bit 30 - TMU reset"]
    #[inline(always)]
    #[must_use]
    pub fn tmurst(&mut self) -> TmurstW<AhbrstSpec> {
        TmurstW::new(self, 30)
    }
    #[doc = "Bit 31 - SQPI reset"]
    #[inline(always)]
    #[must_use]
    pub fn sqpirst(&mut self) -> SqpirstW<AhbrstSpec> {
        SqpirstW::new(self, 31)
    }
}
#[doc = "AHB reset register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`ahbrst::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`ahbrst::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct AhbrstSpec;
impl crate::RegisterSpec for AhbrstSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`ahbrst::R`](R) reader structure"]
impl crate::Readable for AhbrstSpec {}
#[doc = "`write(|w| ..)` method takes [`ahbrst::W`](W) writer structure"]
impl crate::Writable for AhbrstSpec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets AHBRST to value 0"]
impl crate::Resettable for AhbrstSpec {
    const RESET_VALUE: u32 = 0;
}
