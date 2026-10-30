#[doc = "Register `HCH5CTL` reader"]
pub type R = crate::R<Hch5ctlSpec>;
#[doc = "Register `HCH5CTL` writer"]
pub type W = crate::W<Hch5ctlSpec>;
#[doc = "Field `MPL` reader - Maximum packet size"]
pub type MplR = crate::FieldReader<u16>;
#[doc = "Field `MPL` writer - Maximum packet size"]
pub type MplW<'a, REG> = crate::FieldWriter<'a, REG, 11, u16>;
#[doc = "Field `EPNUM` reader - Endpoint number"]
pub type EpnumR = crate::FieldReader;
#[doc = "Field `EPNUM` writer - Endpoint number"]
pub type EpnumW<'a, REG> = crate::FieldWriter<'a, REG, 4>;
#[doc = "Field `EPDIR` reader - Endpoint direction"]
pub type EpdirR = crate::BitReader;
#[doc = "Field `EPDIR` writer - Endpoint direction"]
pub type EpdirW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `LSD` reader - Low-speed device"]
pub type LsdR = crate::BitReader;
#[doc = "Field `LSD` writer - Low-speed device"]
pub type LsdW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `EPTYPE` reader - Endpoint type"]
pub type EptypeR = crate::FieldReader;
#[doc = "Field `EPTYPE` writer - Endpoint type"]
pub type EptypeW<'a, REG> = crate::FieldWriter<'a, REG, 2>;
#[doc = "Field `MPC` reader - Multiple Packet Count"]
pub type MpcR = crate::FieldReader;
#[doc = "Field `MPC` writer - Multiple Packet Count"]
pub type MpcW<'a, REG> = crate::FieldWriter<'a, REG, 2>;
#[doc = "Field `DAR` reader - Device address"]
pub type DarR = crate::FieldReader;
#[doc = "Field `DAR` writer - Device address"]
pub type DarW<'a, REG> = crate::FieldWriter<'a, REG, 7>;
#[doc = "Field `ODDFRM` reader - Odd frame"]
pub type OddfrmR = crate::BitReader;
#[doc = "Field `ODDFRM` writer - Odd frame"]
pub type OddfrmW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `CDIS` reader - Channel disable"]
pub type CdisR = crate::BitReader;
#[doc = "Field `CDIS` writer - Channel disable"]
pub type CdisW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `CEN` reader - Channel enable"]
pub type CenR = crate::BitReader;
#[doc = "Field `CEN` writer - Channel enable"]
pub type CenW<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bits 0:10 - Maximum packet size"]
    #[inline(always)]
    pub fn mpl(&self) -> MplR {
        MplR::new((self.bits & 0x07ff) as u16)
    }
    #[doc = "Bits 11:14 - Endpoint number"]
    #[inline(always)]
    pub fn epnum(&self) -> EpnumR {
        EpnumR::new(((self.bits >> 11) & 0x0f) as u8)
    }
    #[doc = "Bit 15 - Endpoint direction"]
    #[inline(always)]
    pub fn epdir(&self) -> EpdirR {
        EpdirR::new(((self.bits >> 15) & 1) != 0)
    }
    #[doc = "Bit 17 - Low-speed device"]
    #[inline(always)]
    pub fn lsd(&self) -> LsdR {
        LsdR::new(((self.bits >> 17) & 1) != 0)
    }
    #[doc = "Bits 18:19 - Endpoint type"]
    #[inline(always)]
    pub fn eptype(&self) -> EptypeR {
        EptypeR::new(((self.bits >> 18) & 3) as u8)
    }
    #[doc = "Bits 20:21 - Multiple Packet Count"]
    #[inline(always)]
    pub fn mpc(&self) -> MpcR {
        MpcR::new(((self.bits >> 20) & 3) as u8)
    }
    #[doc = "Bits 22:28 - Device address"]
    #[inline(always)]
    pub fn dar(&self) -> DarR {
        DarR::new(((self.bits >> 22) & 0x7f) as u8)
    }
    #[doc = "Bit 29 - Odd frame"]
    #[inline(always)]
    pub fn oddfrm(&self) -> OddfrmR {
        OddfrmR::new(((self.bits >> 29) & 1) != 0)
    }
    #[doc = "Bit 30 - Channel disable"]
    #[inline(always)]
    pub fn cdis(&self) -> CdisR {
        CdisR::new(((self.bits >> 30) & 1) != 0)
    }
    #[doc = "Bit 31 - Channel enable"]
    #[inline(always)]
    pub fn cen(&self) -> CenR {
        CenR::new(((self.bits >> 31) & 1) != 0)
    }
}
impl W {
    #[doc = "Bits 0:10 - Maximum packet size"]
    #[inline(always)]
    #[must_use]
    pub fn mpl(&mut self) -> MplW<Hch5ctlSpec> {
        MplW::new(self, 0)
    }
    #[doc = "Bits 11:14 - Endpoint number"]
    #[inline(always)]
    #[must_use]
    pub fn epnum(&mut self) -> EpnumW<Hch5ctlSpec> {
        EpnumW::new(self, 11)
    }
    #[doc = "Bit 15 - Endpoint direction"]
    #[inline(always)]
    #[must_use]
    pub fn epdir(&mut self) -> EpdirW<Hch5ctlSpec> {
        EpdirW::new(self, 15)
    }
    #[doc = "Bit 17 - Low-speed device"]
    #[inline(always)]
    #[must_use]
    pub fn lsd(&mut self) -> LsdW<Hch5ctlSpec> {
        LsdW::new(self, 17)
    }
    #[doc = "Bits 18:19 - Endpoint type"]
    #[inline(always)]
    #[must_use]
    pub fn eptype(&mut self) -> EptypeW<Hch5ctlSpec> {
        EptypeW::new(self, 18)
    }
    #[doc = "Bits 20:21 - Multiple Packet Count"]
    #[inline(always)]
    #[must_use]
    pub fn mpc(&mut self) -> MpcW<Hch5ctlSpec> {
        MpcW::new(self, 20)
    }
    #[doc = "Bits 22:28 - Device address"]
    #[inline(always)]
    #[must_use]
    pub fn dar(&mut self) -> DarW<Hch5ctlSpec> {
        DarW::new(self, 22)
    }
    #[doc = "Bit 29 - Odd frame"]
    #[inline(always)]
    #[must_use]
    pub fn oddfrm(&mut self) -> OddfrmW<Hch5ctlSpec> {
        OddfrmW::new(self, 29)
    }
    #[doc = "Bit 30 - Channel disable"]
    #[inline(always)]
    #[must_use]
    pub fn cdis(&mut self) -> CdisW<Hch5ctlSpec> {
        CdisW::new(self, 30)
    }
    #[doc = "Bit 31 - Channel enable"]
    #[inline(always)]
    #[must_use]
    pub fn cen(&mut self) -> CenW<Hch5ctlSpec> {
        CenW::new(self, 31)
    }
}
#[doc = "host channel-5 characteristics register (HCH5CTL)\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`hch5ctl::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`hch5ctl::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct Hch5ctlSpec;
impl crate::RegisterSpec for Hch5ctlSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`hch5ctl::R`](R) reader structure"]
impl crate::Readable for Hch5ctlSpec {}
#[doc = "`write(|w| ..)` method takes [`hch5ctl::W`](W) writer structure"]
impl crate::Writable for Hch5ctlSpec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets HCH5CTL to value 0"]
impl crate::Resettable for Hch5ctlSpec {
    const RESET_VALUE: u32 = 0;
}
