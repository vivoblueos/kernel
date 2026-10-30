#[doc = "Register `ADDCTL` reader"]
pub type R = crate::R<AddctlSpec>;
#[doc = "Register `ADDCTL` writer"]
pub type W = crate::W<AddctlSpec>;
#[doc = "Field `CK48MSEL` reader - 48MHz clock selection"]
pub type Ck48mselR = crate::FieldReader;
#[doc = "Field `CK48MSEL` writer - 48MHz clock selection"]
pub type Ck48mselW<'a, REG> = crate::FieldWriter<'a, REG, 2>;
#[doc = "Field `USBHSSEL` reader - USBHS clock divider factor"]
pub type UsbhsselR = crate::BitReader;
#[doc = "Field `USBHSSEL` writer - USBHS clock divider factor"]
pub type UsbhsselW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `USBHSDV` reader - USBHS clock selection"]
pub type UsbhsdvR = crate::FieldReader;
#[doc = "Field `USBHSDV` writer - USBHS clock selection"]
pub type UsbhsdvW<'a, REG> = crate::FieldWriter<'a, REG, 3>;
#[doc = "Field `USBSWEN` reader - USB clock source selection enable"]
pub type UsbswenR = crate::BitReader;
#[doc = "Field `USBSWEN` writer - USB clock source selection enable"]
pub type UsbswenW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `PLLUSBEN` reader - PLLUSB enable"]
pub type PllusbenR = crate::BitReader;
#[doc = "Field `PLLUSBEN` writer - PLLUSB enable"]
pub type PllusbenW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `PLLUSBSTB` reader - PLLUSB clock stabilization flag"]
pub type PllusbstbR = crate::BitReader;
#[doc = "Field `PLLUSBSTB` writer - PLLUSB clock stabilization flag"]
pub type PllusbstbW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `IRC48MEN` reader - Internal 48MHz RC oscillator enable"]
pub type Irc48menR = crate::BitReader;
#[doc = "Field `IRC48MEN` writer - Internal 48MHz RC oscillator enable"]
pub type Irc48menW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `IRC48MSTB` reader - Internal 48MHz RC oscillator clock stabilization Flag"]
pub type Irc48mstbR = crate::BitReader;
#[doc = "Field `IRC48MCALIB` reader - Internal 48MHz RC oscillator calibration value register"]
pub type Irc48mcalibR = crate::FieldReader;
impl R {
    #[doc = "Bits 0:1 - 48MHz clock selection"]
    #[inline(always)]
    pub fn ck48msel(&self) -> Ck48mselR {
        Ck48mselR::new((self.bits & 3) as u8)
    }
    #[doc = "Bit 2 - USBHS clock divider factor"]
    #[inline(always)]
    pub fn usbhssel(&self) -> UsbhsselR {
        UsbhsselR::new(((self.bits >> 2) & 1) != 0)
    }
    #[doc = "Bits 3:5 - USBHS clock selection"]
    #[inline(always)]
    pub fn usbhsdv(&self) -> UsbhsdvR {
        UsbhsdvR::new(((self.bits >> 3) & 7) as u8)
    }
    #[doc = "Bit 6 - USB clock source selection enable"]
    #[inline(always)]
    pub fn usbswen(&self) -> UsbswenR {
        UsbswenR::new(((self.bits >> 6) & 1) != 0)
    }
    #[doc = "Bit 14 - PLLUSB enable"]
    #[inline(always)]
    pub fn pllusben(&self) -> PllusbenR {
        PllusbenR::new(((self.bits >> 14) & 1) != 0)
    }
    #[doc = "Bit 15 - PLLUSB clock stabilization flag"]
    #[inline(always)]
    pub fn pllusbstb(&self) -> PllusbstbR {
        PllusbstbR::new(((self.bits >> 15) & 1) != 0)
    }
    #[doc = "Bit 16 - Internal 48MHz RC oscillator enable"]
    #[inline(always)]
    pub fn irc48men(&self) -> Irc48menR {
        Irc48menR::new(((self.bits >> 16) & 1) != 0)
    }
    #[doc = "Bit 17 - Internal 48MHz RC oscillator clock stabilization Flag"]
    #[inline(always)]
    pub fn irc48mstb(&self) -> Irc48mstbR {
        Irc48mstbR::new(((self.bits >> 17) & 1) != 0)
    }
    #[doc = "Bits 24:31 - Internal 48MHz RC oscillator calibration value register"]
    #[inline(always)]
    pub fn irc48mcalib(&self) -> Irc48mcalibR {
        Irc48mcalibR::new(((self.bits >> 24) & 0xff) as u8)
    }
}
impl W {
    #[doc = "Bits 0:1 - 48MHz clock selection"]
    #[inline(always)]
    #[must_use]
    pub fn ck48msel(&mut self) -> Ck48mselW<AddctlSpec> {
        Ck48mselW::new(self, 0)
    }
    #[doc = "Bit 2 - USBHS clock divider factor"]
    #[inline(always)]
    #[must_use]
    pub fn usbhssel(&mut self) -> UsbhsselW<AddctlSpec> {
        UsbhsselW::new(self, 2)
    }
    #[doc = "Bits 3:5 - USBHS clock selection"]
    #[inline(always)]
    #[must_use]
    pub fn usbhsdv(&mut self) -> UsbhsdvW<AddctlSpec> {
        UsbhsdvW::new(self, 3)
    }
    #[doc = "Bit 6 - USB clock source selection enable"]
    #[inline(always)]
    #[must_use]
    pub fn usbswen(&mut self) -> UsbswenW<AddctlSpec> {
        UsbswenW::new(self, 6)
    }
    #[doc = "Bit 14 - PLLUSB enable"]
    #[inline(always)]
    #[must_use]
    pub fn pllusben(&mut self) -> PllusbenW<AddctlSpec> {
        PllusbenW::new(self, 14)
    }
    #[doc = "Bit 15 - PLLUSB clock stabilization flag"]
    #[inline(always)]
    #[must_use]
    pub fn pllusbstb(&mut self) -> PllusbstbW<AddctlSpec> {
        PllusbstbW::new(self, 15)
    }
    #[doc = "Bit 16 - Internal 48MHz RC oscillator enable"]
    #[inline(always)]
    #[must_use]
    pub fn irc48men(&mut self) -> Irc48menW<AddctlSpec> {
        Irc48menW::new(self, 16)
    }
}
#[doc = "Additional clock control register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`addctl::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`addctl::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct AddctlSpec;
impl crate::RegisterSpec for AddctlSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`addctl::R`](R) reader structure"]
impl crate::Readable for AddctlSpec {}
#[doc = "`write(|w| ..)` method takes [`addctl::W`](W) writer structure"]
impl crate::Writable for AddctlSpec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets ADDCTL to value 0x8000_0000"]
impl crate::Resettable for AddctlSpec {
    const RESET_VALUE: u32 = 0x8000_0000;
}
