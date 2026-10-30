#[doc = "Register `BDCTL` reader"]
pub type R = crate::R<BdctlSpec>;
#[doc = "Register `BDCTL` writer"]
pub type W = crate::W<BdctlSpec>;
#[doc = "Field `LXTALEN` reader - LXTAL enable"]
pub type LxtalenR = crate::BitReader;
#[doc = "Field `LXTALEN` writer - LXTAL enable"]
pub type LxtalenW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `LXTALSTB` reader - External low-speed oscillator stabilization"]
pub type LxtalstbR = crate::BitReader;
#[doc = "Field `LXTALBPS` reader - LXTAL bypass mode enable"]
pub type LxtalbpsR = crate::BitReader;
#[doc = "Field `LXTALBPS` writer - LXTAL bypass mode enable"]
pub type LxtalbpsW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `LXTALDRI` reader - LXTAL drive capability"]
pub type LxtaldriR = crate::FieldReader;
#[doc = "Field `LXTALDRI` writer - LXTAL drive capability"]
pub type LxtaldriW<'a, REG> = crate::FieldWriter<'a, REG, 2>;
#[doc = "Field `RTCSRC` reader - RTC clock entry selection"]
pub type RtcsrcR = crate::FieldReader;
#[doc = "Field `RTCSRC` writer - RTC clock entry selection"]
pub type RtcsrcW<'a, REG> = crate::FieldWriter<'a, REG, 2>;
#[doc = "Field `RTCEN` reader - RTC clock enable"]
pub type RtcenR = crate::BitReader;
#[doc = "Field `RTCEN` writer - RTC clock enable"]
pub type RtcenW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `BKPRST` reader - Backup domain reset"]
pub type BkprstR = crate::BitReader;
#[doc = "Field `BKPRST` writer - Backup domain reset"]
pub type BkprstW<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 0 - LXTAL enable"]
    #[inline(always)]
    pub fn lxtalen(&self) -> LxtalenR {
        LxtalenR::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - External low-speed oscillator stabilization"]
    #[inline(always)]
    pub fn lxtalstb(&self) -> LxtalstbR {
        LxtalstbR::new(((self.bits >> 1) & 1) != 0)
    }
    #[doc = "Bit 2 - LXTAL bypass mode enable"]
    #[inline(always)]
    pub fn lxtalbps(&self) -> LxtalbpsR {
        LxtalbpsR::new(((self.bits >> 2) & 1) != 0)
    }
    #[doc = "Bits 3:4 - LXTAL drive capability"]
    #[inline(always)]
    pub fn lxtaldri(&self) -> LxtaldriR {
        LxtaldriR::new(((self.bits >> 3) & 3) as u8)
    }
    #[doc = "Bits 8:9 - RTC clock entry selection"]
    #[inline(always)]
    pub fn rtcsrc(&self) -> RtcsrcR {
        RtcsrcR::new(((self.bits >> 8) & 3) as u8)
    }
    #[doc = "Bit 15 - RTC clock enable"]
    #[inline(always)]
    pub fn rtcen(&self) -> RtcenR {
        RtcenR::new(((self.bits >> 15) & 1) != 0)
    }
    #[doc = "Bit 16 - Backup domain reset"]
    #[inline(always)]
    pub fn bkprst(&self) -> BkprstR {
        BkprstR::new(((self.bits >> 16) & 1) != 0)
    }
}
impl W {
    #[doc = "Bit 0 - LXTAL enable"]
    #[inline(always)]
    #[must_use]
    pub fn lxtalen(&mut self) -> LxtalenW<BdctlSpec> {
        LxtalenW::new(self, 0)
    }
    #[doc = "Bit 2 - LXTAL bypass mode enable"]
    #[inline(always)]
    #[must_use]
    pub fn lxtalbps(&mut self) -> LxtalbpsW<BdctlSpec> {
        LxtalbpsW::new(self, 2)
    }
    #[doc = "Bits 3:4 - LXTAL drive capability"]
    #[inline(always)]
    #[must_use]
    pub fn lxtaldri(&mut self) -> LxtaldriW<BdctlSpec> {
        LxtaldriW::new(self, 3)
    }
    #[doc = "Bits 8:9 - RTC clock entry selection"]
    #[inline(always)]
    #[must_use]
    pub fn rtcsrc(&mut self) -> RtcsrcW<BdctlSpec> {
        RtcsrcW::new(self, 8)
    }
    #[doc = "Bit 15 - RTC clock enable"]
    #[inline(always)]
    #[must_use]
    pub fn rtcen(&mut self) -> RtcenW<BdctlSpec> {
        RtcenW::new(self, 15)
    }
    #[doc = "Bit 16 - Backup domain reset"]
    #[inline(always)]
    #[must_use]
    pub fn bkprst(&mut self) -> BkprstW<BdctlSpec> {
        BkprstW::new(self, 16)
    }
}
#[doc = "Backup domain control register (RCU_BDCTL)\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`bdctl::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`bdctl::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct BdctlSpec;
impl crate::RegisterSpec for BdctlSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`bdctl::R`](R) reader structure"]
impl crate::Readable for BdctlSpec {}
#[doc = "`write(|w| ..)` method takes [`bdctl::W`](W) writer structure"]
impl crate::Writable for BdctlSpec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets BDCTL to value 0x18"]
impl crate::Resettable for BdctlSpec {
    const RESET_VALUE: u32 = 0x18;
}
