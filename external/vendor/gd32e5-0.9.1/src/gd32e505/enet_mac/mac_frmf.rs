#[doc = "Register `MAC_FRMF` reader"]
pub type R = crate::R<MacFrmfSpec>;
#[doc = "Register `MAC_FRMF` writer"]
pub type W = crate::W<MacFrmfSpec>;
#[doc = "Field `PM` reader - Promiscuous mode"]
pub type PmR = crate::BitReader;
#[doc = "Field `PM` writer - Promiscuous mode"]
pub type PmW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `HUF` reader - Hash unicast filter"]
pub type HufR = crate::BitReader;
#[doc = "Field `HUF` writer - Hash unicast filter"]
pub type HufW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `HMF` reader - Hash multicast filter"]
pub type HmfR = crate::BitReader;
#[doc = "Field `HMF` writer - Hash multicast filter"]
pub type HmfW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `DAIFLT` reader - Destination address inverse filtering"]
pub type DaifltR = crate::BitReader;
#[doc = "Field `DAIFLT` writer - Destination address inverse filtering"]
pub type DaifltW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `MFD` reader - multicast filter disable"]
pub type MfdR = crate::BitReader;
#[doc = "Field `MFD` writer - multicast filter disable"]
pub type MfdW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `BFRMD` reader - Broadcast frames disable"]
pub type BfrmdR = crate::BitReader;
#[doc = "Field `BFRMD` writer - Broadcast frames disable"]
pub type BfrmdW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `PCFRM` reader - Pass control frames"]
pub type PcfrmR = crate::FieldReader;
#[doc = "Field `PCFRM` writer - Pass control frames"]
pub type PcfrmW<'a, REG> = crate::FieldWriter<'a, REG, 2>;
#[doc = "Field `SAIFLT` reader - Source address inverse filtering"]
pub type SaifltR = crate::BitReader;
#[doc = "Field `SAIFLT` writer - Source address inverse filtering"]
pub type SaifltW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SAFLT` reader - Source address filter"]
pub type SafltR = crate::BitReader;
#[doc = "Field `SAFLT` writer - Source address filter"]
pub type SafltW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `HPFLT` reader - Hash or perfect filter"]
pub type HpfltR = crate::BitReader;
#[doc = "Field `HPFLT` writer - Hash or perfect filter"]
pub type HpfltW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `FAR` reader - Frames all receive"]
pub type FarR = crate::BitReader;
#[doc = "Field `FAR` writer - Frames all receive"]
pub type FarW<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 0 - Promiscuous mode"]
    #[inline(always)]
    pub fn pm(&self) -> PmR {
        PmR::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - Hash unicast filter"]
    #[inline(always)]
    pub fn huf(&self) -> HufR {
        HufR::new(((self.bits >> 1) & 1) != 0)
    }
    #[doc = "Bit 2 - Hash multicast filter"]
    #[inline(always)]
    pub fn hmf(&self) -> HmfR {
        HmfR::new(((self.bits >> 2) & 1) != 0)
    }
    #[doc = "Bit 3 - Destination address inverse filtering"]
    #[inline(always)]
    pub fn daiflt(&self) -> DaifltR {
        DaifltR::new(((self.bits >> 3) & 1) != 0)
    }
    #[doc = "Bit 4 - multicast filter disable"]
    #[inline(always)]
    pub fn mfd(&self) -> MfdR {
        MfdR::new(((self.bits >> 4) & 1) != 0)
    }
    #[doc = "Bit 5 - Broadcast frames disable"]
    #[inline(always)]
    pub fn bfrmd(&self) -> BfrmdR {
        BfrmdR::new(((self.bits >> 5) & 1) != 0)
    }
    #[doc = "Bits 6:7 - Pass control frames"]
    #[inline(always)]
    pub fn pcfrm(&self) -> PcfrmR {
        PcfrmR::new(((self.bits >> 6) & 3) as u8)
    }
    #[doc = "Bit 8 - Source address inverse filtering"]
    #[inline(always)]
    pub fn saiflt(&self) -> SaifltR {
        SaifltR::new(((self.bits >> 8) & 1) != 0)
    }
    #[doc = "Bit 9 - Source address filter"]
    #[inline(always)]
    pub fn saflt(&self) -> SafltR {
        SafltR::new(((self.bits >> 9) & 1) != 0)
    }
    #[doc = "Bit 10 - Hash or perfect filter"]
    #[inline(always)]
    pub fn hpflt(&self) -> HpfltR {
        HpfltR::new(((self.bits >> 10) & 1) != 0)
    }
    #[doc = "Bit 31 - Frames all receive"]
    #[inline(always)]
    pub fn far(&self) -> FarR {
        FarR::new(((self.bits >> 31) & 1) != 0)
    }
}
impl W {
    #[doc = "Bit 0 - Promiscuous mode"]
    #[inline(always)]
    #[must_use]
    pub fn pm(&mut self) -> PmW<MacFrmfSpec> {
        PmW::new(self, 0)
    }
    #[doc = "Bit 1 - Hash unicast filter"]
    #[inline(always)]
    #[must_use]
    pub fn huf(&mut self) -> HufW<MacFrmfSpec> {
        HufW::new(self, 1)
    }
    #[doc = "Bit 2 - Hash multicast filter"]
    #[inline(always)]
    #[must_use]
    pub fn hmf(&mut self) -> HmfW<MacFrmfSpec> {
        HmfW::new(self, 2)
    }
    #[doc = "Bit 3 - Destination address inverse filtering"]
    #[inline(always)]
    #[must_use]
    pub fn daiflt(&mut self) -> DaifltW<MacFrmfSpec> {
        DaifltW::new(self, 3)
    }
    #[doc = "Bit 4 - multicast filter disable"]
    #[inline(always)]
    #[must_use]
    pub fn mfd(&mut self) -> MfdW<MacFrmfSpec> {
        MfdW::new(self, 4)
    }
    #[doc = "Bit 5 - Broadcast frames disable"]
    #[inline(always)]
    #[must_use]
    pub fn bfrmd(&mut self) -> BfrmdW<MacFrmfSpec> {
        BfrmdW::new(self, 5)
    }
    #[doc = "Bits 6:7 - Pass control frames"]
    #[inline(always)]
    #[must_use]
    pub fn pcfrm(&mut self) -> PcfrmW<MacFrmfSpec> {
        PcfrmW::new(self, 6)
    }
    #[doc = "Bit 8 - Source address inverse filtering"]
    #[inline(always)]
    #[must_use]
    pub fn saiflt(&mut self) -> SaifltW<MacFrmfSpec> {
        SaifltW::new(self, 8)
    }
    #[doc = "Bit 9 - Source address filter"]
    #[inline(always)]
    #[must_use]
    pub fn saflt(&mut self) -> SafltW<MacFrmfSpec> {
        SafltW::new(self, 9)
    }
    #[doc = "Bit 10 - Hash or perfect filter"]
    #[inline(always)]
    #[must_use]
    pub fn hpflt(&mut self) -> HpfltW<MacFrmfSpec> {
        HpfltW::new(self, 10)
    }
    #[doc = "Bit 31 - Frames all receive"]
    #[inline(always)]
    #[must_use]
    pub fn far(&mut self) -> FarW<MacFrmfSpec> {
        FarW::new(self, 31)
    }
}
#[doc = "Ethernet MAC frame filter register (MAC_FRMF)\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`mac_frmf::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`mac_frmf::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct MacFrmfSpec;
impl crate::RegisterSpec for MacFrmfSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`mac_frmf::R`](R) reader structure"]
impl crate::Readable for MacFrmfSpec {}
#[doc = "`write(|w| ..)` method takes [`mac_frmf::W`](W) writer structure"]
impl crate::Writable for MacFrmfSpec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets MAC_FRMF to value 0"]
impl crate::Resettable for MacFrmfSpec {
    const RESET_VALUE: u32 = 0;
}
