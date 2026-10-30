#[doc = "Register `MAC_CFG` reader"]
pub type R = crate::R<MacCfgSpec>;
#[doc = "Register `MAC_CFG` writer"]
pub type W = crate::W<MacCfgSpec>;
#[doc = "Field `REN` reader - Receiver enable"]
pub type RenR = crate::BitReader;
#[doc = "Field `REN` writer - Receiver enable"]
pub type RenW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `TEN` reader - Transmitter enable"]
pub type TenR = crate::BitReader;
#[doc = "Field `TEN` writer - Transmitter enable"]
pub type TenW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `DFC` reader - Deferral check"]
pub type DfcR = crate::BitReader;
#[doc = "Field `DFC` writer - Deferral check"]
pub type DfcW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `BOL` reader - Back-off limit"]
pub type BolR = crate::FieldReader;
#[doc = "Field `BOL` writer - Back-off limit"]
pub type BolW<'a, REG> = crate::FieldWriter<'a, REG, 2>;
#[doc = "Field `APCD` reader - Automatic pad/CRC drop"]
pub type ApcdR = crate::BitReader;
#[doc = "Field `APCD` writer - Automatic pad/CRC drop"]
pub type ApcdW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `RTD` reader - Retry disable"]
pub type RtdR = crate::BitReader;
#[doc = "Field `RTD` writer - Retry disable"]
pub type RtdW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `IPFCO` reader - IP frame checksum offload"]
pub type IpfcoR = crate::BitReader;
#[doc = "Field `IPFCO` writer - IP frame checksum offload"]
pub type IpfcoW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `DPM` reader - Duplex mode"]
pub type DpmR = crate::BitReader;
#[doc = "Field `DPM` writer - Duplex mode"]
pub type DpmW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `LBM` reader - Loopback mode"]
pub type LbmR = crate::BitReader;
#[doc = "Field `LBM` writer - Loopback mode"]
pub type LbmW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ROD` reader - Receive own disable"]
pub type RodR = crate::BitReader;
#[doc = "Field `ROD` writer - Receive own disable"]
pub type RodW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SPD` reader - Fast Ethernet speed"]
pub type SpdR = crate::BitReader;
#[doc = "Field `SPD` writer - Fast Ethernet speed"]
pub type SpdW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `CSD` reader - Carrier sense disable"]
pub type CsdR = crate::BitReader;
#[doc = "Field `CSD` writer - Carrier sense disable"]
pub type CsdW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `IGBS` reader - Inter frame gap bit selection"]
pub type IgbsR = crate::FieldReader;
#[doc = "Field `IGBS` writer - Inter frame gap bit selection"]
pub type IgbsW<'a, REG> = crate::FieldWriter<'a, REG, 3>;
#[doc = "Field `JBD` reader - Jabber disable"]
pub type JbdR = crate::BitReader;
#[doc = "Field `JBD` writer - Jabber disable"]
pub type JbdW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `WDD` reader - Watchdog disable"]
pub type WddR = crate::BitReader;
#[doc = "Field `WDD` writer - Watchdog disable"]
pub type WddW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `TFCD` reader - Type Frame CRC Dropping"]
pub type TfcdR = crate::BitReader;
#[doc = "Field `TFCD` writer - Type Frame CRC Dropping"]
pub type TfcdW<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 2 - Receiver enable"]
    #[inline(always)]
    pub fn ren(&self) -> RenR {
        RenR::new(((self.bits >> 2) & 1) != 0)
    }
    #[doc = "Bit 3 - Transmitter enable"]
    #[inline(always)]
    pub fn ten(&self) -> TenR {
        TenR::new(((self.bits >> 3) & 1) != 0)
    }
    #[doc = "Bit 4 - Deferral check"]
    #[inline(always)]
    pub fn dfc(&self) -> DfcR {
        DfcR::new(((self.bits >> 4) & 1) != 0)
    }
    #[doc = "Bits 5:6 - Back-off limit"]
    #[inline(always)]
    pub fn bol(&self) -> BolR {
        BolR::new(((self.bits >> 5) & 3) as u8)
    }
    #[doc = "Bit 7 - Automatic pad/CRC drop"]
    #[inline(always)]
    pub fn apcd(&self) -> ApcdR {
        ApcdR::new(((self.bits >> 7) & 1) != 0)
    }
    #[doc = "Bit 9 - Retry disable"]
    #[inline(always)]
    pub fn rtd(&self) -> RtdR {
        RtdR::new(((self.bits >> 9) & 1) != 0)
    }
    #[doc = "Bit 10 - IP frame checksum offload"]
    #[inline(always)]
    pub fn ipfco(&self) -> IpfcoR {
        IpfcoR::new(((self.bits >> 10) & 1) != 0)
    }
    #[doc = "Bit 11 - Duplex mode"]
    #[inline(always)]
    pub fn dpm(&self) -> DpmR {
        DpmR::new(((self.bits >> 11) & 1) != 0)
    }
    #[doc = "Bit 12 - Loopback mode"]
    #[inline(always)]
    pub fn lbm(&self) -> LbmR {
        LbmR::new(((self.bits >> 12) & 1) != 0)
    }
    #[doc = "Bit 13 - Receive own disable"]
    #[inline(always)]
    pub fn rod(&self) -> RodR {
        RodR::new(((self.bits >> 13) & 1) != 0)
    }
    #[doc = "Bit 14 - Fast Ethernet speed"]
    #[inline(always)]
    pub fn spd(&self) -> SpdR {
        SpdR::new(((self.bits >> 14) & 1) != 0)
    }
    #[doc = "Bit 16 - Carrier sense disable"]
    #[inline(always)]
    pub fn csd(&self) -> CsdR {
        CsdR::new(((self.bits >> 16) & 1) != 0)
    }
    #[doc = "Bits 17:19 - Inter frame gap bit selection"]
    #[inline(always)]
    pub fn igbs(&self) -> IgbsR {
        IgbsR::new(((self.bits >> 17) & 7) as u8)
    }
    #[doc = "Bit 22 - Jabber disable"]
    #[inline(always)]
    pub fn jbd(&self) -> JbdR {
        JbdR::new(((self.bits >> 22) & 1) != 0)
    }
    #[doc = "Bit 23 - Watchdog disable"]
    #[inline(always)]
    pub fn wdd(&self) -> WddR {
        WddR::new(((self.bits >> 23) & 1) != 0)
    }
    #[doc = "Bit 25 - Type Frame CRC Dropping"]
    #[inline(always)]
    pub fn tfcd(&self) -> TfcdR {
        TfcdR::new(((self.bits >> 25) & 1) != 0)
    }
}
impl W {
    #[doc = "Bit 2 - Receiver enable"]
    #[inline(always)]
    #[must_use]
    pub fn ren(&mut self) -> RenW<MacCfgSpec> {
        RenW::new(self, 2)
    }
    #[doc = "Bit 3 - Transmitter enable"]
    #[inline(always)]
    #[must_use]
    pub fn ten(&mut self) -> TenW<MacCfgSpec> {
        TenW::new(self, 3)
    }
    #[doc = "Bit 4 - Deferral check"]
    #[inline(always)]
    #[must_use]
    pub fn dfc(&mut self) -> DfcW<MacCfgSpec> {
        DfcW::new(self, 4)
    }
    #[doc = "Bits 5:6 - Back-off limit"]
    #[inline(always)]
    #[must_use]
    pub fn bol(&mut self) -> BolW<MacCfgSpec> {
        BolW::new(self, 5)
    }
    #[doc = "Bit 7 - Automatic pad/CRC drop"]
    #[inline(always)]
    #[must_use]
    pub fn apcd(&mut self) -> ApcdW<MacCfgSpec> {
        ApcdW::new(self, 7)
    }
    #[doc = "Bit 9 - Retry disable"]
    #[inline(always)]
    #[must_use]
    pub fn rtd(&mut self) -> RtdW<MacCfgSpec> {
        RtdW::new(self, 9)
    }
    #[doc = "Bit 10 - IP frame checksum offload"]
    #[inline(always)]
    #[must_use]
    pub fn ipfco(&mut self) -> IpfcoW<MacCfgSpec> {
        IpfcoW::new(self, 10)
    }
    #[doc = "Bit 11 - Duplex mode"]
    #[inline(always)]
    #[must_use]
    pub fn dpm(&mut self) -> DpmW<MacCfgSpec> {
        DpmW::new(self, 11)
    }
    #[doc = "Bit 12 - Loopback mode"]
    #[inline(always)]
    #[must_use]
    pub fn lbm(&mut self) -> LbmW<MacCfgSpec> {
        LbmW::new(self, 12)
    }
    #[doc = "Bit 13 - Receive own disable"]
    #[inline(always)]
    #[must_use]
    pub fn rod(&mut self) -> RodW<MacCfgSpec> {
        RodW::new(self, 13)
    }
    #[doc = "Bit 14 - Fast Ethernet speed"]
    #[inline(always)]
    #[must_use]
    pub fn spd(&mut self) -> SpdW<MacCfgSpec> {
        SpdW::new(self, 14)
    }
    #[doc = "Bit 16 - Carrier sense disable"]
    #[inline(always)]
    #[must_use]
    pub fn csd(&mut self) -> CsdW<MacCfgSpec> {
        CsdW::new(self, 16)
    }
    #[doc = "Bits 17:19 - Inter frame gap bit selection"]
    #[inline(always)]
    #[must_use]
    pub fn igbs(&mut self) -> IgbsW<MacCfgSpec> {
        IgbsW::new(self, 17)
    }
    #[doc = "Bit 22 - Jabber disable"]
    #[inline(always)]
    #[must_use]
    pub fn jbd(&mut self) -> JbdW<MacCfgSpec> {
        JbdW::new(self, 22)
    }
    #[doc = "Bit 23 - Watchdog disable"]
    #[inline(always)]
    #[must_use]
    pub fn wdd(&mut self) -> WddW<MacCfgSpec> {
        WddW::new(self, 23)
    }
    #[doc = "Bit 25 - Type Frame CRC Dropping"]
    #[inline(always)]
    #[must_use]
    pub fn tfcd(&mut self) -> TfcdW<MacCfgSpec> {
        TfcdW::new(self, 25)
    }
}
#[doc = "Ethernet MAC configuration register (MAC_CFG)\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`mac_cfg::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`mac_cfg::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct MacCfgSpec;
impl crate::RegisterSpec for MacCfgSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`mac_cfg::R`](R) reader structure"]
impl crate::Readable for MacCfgSpec {}
#[doc = "`write(|w| ..)` method takes [`mac_cfg::W`](W) writer structure"]
impl crate::Writable for MacCfgSpec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets MAC_CFG to value 0x8000"]
impl crate::Resettable for MacCfgSpec {
    const RESET_VALUE: u32 = 0x8000;
}
