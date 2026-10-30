#[doc = "Register `RSTSCK` reader"]
pub type R = crate::R<RstsckSpec>;
#[doc = "Register `RSTSCK` writer"]
pub type W = crate::W<RstsckSpec>;
#[doc = "Field `IRC40KEN` reader - IRC40K enable"]
pub type Irc40kenR = crate::BitReader;
#[doc = "Field `IRC40KEN` writer - IRC40K enable"]
pub type Irc40kenW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `IRC40KSTB` reader - IRC40K stabilization"]
pub type Irc40kstbR = crate::BitReader;
#[doc = "Field `RSTFC` reader - Reset flag clear"]
pub type RstfcR = crate::BitReader;
#[doc = "Field `RSTFC` writer - Reset flag clear"]
pub type RstfcW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `BORRSTF` reader - BORt flag clear"]
pub type BorrstfR = crate::BitReader;
#[doc = "Field `BORRSTF` writer - BORt flag clear"]
pub type BorrstfW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `EPRSTF` reader - External PIN reset flag"]
pub type EprstfR = crate::BitReader;
#[doc = "Field `PORRSTF` reader - Power reset flag"]
pub type PorrstfR = crate::BitReader;
#[doc = "Field `SWRSTF` reader - Software reset flag"]
pub type SwrstfR = crate::BitReader;
#[doc = "Field `FWDGTRSTF` reader - Free Watchdog timer reset flag"]
pub type FwdgtrstfR = crate::BitReader;
#[doc = "Field `WWDGTRSTF` reader - Window watchdog timer reset flag"]
pub type WwdgtrstfR = crate::BitReader;
#[doc = "Field `LPRSTF` reader - Low-power reset flag"]
pub type LprstfR = crate::BitReader;
impl R {
    #[doc = "Bit 0 - IRC40K enable"]
    #[inline(always)]
    pub fn irc40ken(&self) -> Irc40kenR {
        Irc40kenR::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - IRC40K stabilization"]
    #[inline(always)]
    pub fn irc40kstb(&self) -> Irc40kstbR {
        Irc40kstbR::new(((self.bits >> 1) & 1) != 0)
    }
    #[doc = "Bit 24 - Reset flag clear"]
    #[inline(always)]
    pub fn rstfc(&self) -> RstfcR {
        RstfcR::new(((self.bits >> 24) & 1) != 0)
    }
    #[doc = "Bit 25 - BORt flag clear"]
    #[inline(always)]
    pub fn borrstf(&self) -> BorrstfR {
        BorrstfR::new(((self.bits >> 25) & 1) != 0)
    }
    #[doc = "Bit 26 - External PIN reset flag"]
    #[inline(always)]
    pub fn eprstf(&self) -> EprstfR {
        EprstfR::new(((self.bits >> 26) & 1) != 0)
    }
    #[doc = "Bit 27 - Power reset flag"]
    #[inline(always)]
    pub fn porrstf(&self) -> PorrstfR {
        PorrstfR::new(((self.bits >> 27) & 1) != 0)
    }
    #[doc = "Bit 28 - Software reset flag"]
    #[inline(always)]
    pub fn swrstf(&self) -> SwrstfR {
        SwrstfR::new(((self.bits >> 28) & 1) != 0)
    }
    #[doc = "Bit 29 - Free Watchdog timer reset flag"]
    #[inline(always)]
    pub fn fwdgtrstf(&self) -> FwdgtrstfR {
        FwdgtrstfR::new(((self.bits >> 29) & 1) != 0)
    }
    #[doc = "Bit 30 - Window watchdog timer reset flag"]
    #[inline(always)]
    pub fn wwdgtrstf(&self) -> WwdgtrstfR {
        WwdgtrstfR::new(((self.bits >> 30) & 1) != 0)
    }
    #[doc = "Bit 31 - Low-power reset flag"]
    #[inline(always)]
    pub fn lprstf(&self) -> LprstfR {
        LprstfR::new(((self.bits >> 31) & 1) != 0)
    }
}
impl W {
    #[doc = "Bit 0 - IRC40K enable"]
    #[inline(always)]
    #[must_use]
    pub fn irc40ken(&mut self) -> Irc40kenW<RstsckSpec> {
        Irc40kenW::new(self, 0)
    }
    #[doc = "Bit 24 - Reset flag clear"]
    #[inline(always)]
    #[must_use]
    pub fn rstfc(&mut self) -> RstfcW<RstsckSpec> {
        RstfcW::new(self, 24)
    }
    #[doc = "Bit 25 - BORt flag clear"]
    #[inline(always)]
    #[must_use]
    pub fn borrstf(&mut self) -> BorrstfW<RstsckSpec> {
        BorrstfW::new(self, 25)
    }
}
#[doc = "Reset source /clock register (RCU_RSTSCK)\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`rstsck::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`rstsck::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct RstsckSpec;
impl crate::RegisterSpec for RstsckSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`rstsck::R`](R) reader structure"]
impl crate::Readable for RstsckSpec {}
#[doc = "`write(|w| ..)` method takes [`rstsck::W`](W) writer structure"]
impl crate::Writable for RstsckSpec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets RSTSCK to value 0x0c00_0000"]
impl crate::Resettable for RstsckSpec {
    const RESET_VALUE: u32 = 0x0c00_0000;
}
