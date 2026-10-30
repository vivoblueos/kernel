#[doc = "Register `CTL0` reader"]
pub type R = crate::R<Ctl0Spec>;
#[doc = "Register `CTL0` writer"]
pub type W = crate::W<Ctl0Spec>;
#[doc = "Field `LDOLP` reader - LDO Low Power Mode"]
pub type LdolpR = crate::BitReader;
#[doc = "Field `LDOLP` writer - LDO Low Power Mode"]
pub type LdolpW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `STBMOD` reader - Standby Mode"]
pub type StbmodR = crate::BitReader;
#[doc = "Field `STBMOD` writer - Standby Mode"]
pub type StbmodW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `WURST` reader - Wakeup Flag Reset"]
pub type WurstR = crate::BitReader;
#[doc = "Field `WURST` writer - Wakeup Flag Reset"]
pub type WurstW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `STBRST` reader - Standby Flag Reset"]
pub type StbrstR = crate::BitReader;
#[doc = "Field `STBRST` writer - Standby Flag Reset"]
pub type StbrstW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `LVDEN` reader - Low Voltage Detector Enable"]
pub type LvdenR = crate::BitReader;
#[doc = "Field `LVDEN` writer - Low Voltage Detector Enable"]
pub type LvdenW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `LVDT` reader - Low Voltage Detector Threshold"]
pub type LvdtR = crate::FieldReader;
#[doc = "Field `LVDT` writer - Low Voltage Detector Threshold"]
pub type LvdtW<'a, REG> = crate::FieldWriter<'a, REG, 3>;
#[doc = "Field `BKPWEN` reader - Backup Domain Write Enable"]
pub type BkpwenR = crate::BitReader;
#[doc = "Field `BKPWEN` writer - Backup Domain Write Enable"]
pub type BkpwenW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `LDLP` reader - Low-driver mode when use low power LDO."]
pub type LdlpR = crate::BitReader;
#[doc = "Field `LDLP` writer - Low-driver mode when use low power LDO."]
pub type LdlpW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `LDNP` reader - Low-driver mode when use normal power LDO"]
pub type LdnpR = crate::BitReader;
#[doc = "Field `LDNP` writer - Low-driver mode when use normal power LDO"]
pub type LdnpW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `HDEN` reader - High-driver mode enable"]
pub type HdenR = crate::BitReader;
#[doc = "Field `HDEN` writer - High-driver mode enable"]
pub type HdenW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `HDS` reader - High-driver mode switch"]
pub type HdsR = crate::BitReader;
#[doc = "Field `HDS` writer - High-driver mode switch"]
pub type HdsW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `LDEN` reader - Low-driver mode enable in Deep-sleep mode"]
pub type LdenR = crate::FieldReader;
#[doc = "Field `LDEN` writer - Low-driver mode enable in Deep-sleep mode"]
pub type LdenW<'a, REG> = crate::FieldWriter<'a, REG, 2>;
impl R {
    #[doc = "Bit 0 - LDO Low Power Mode"]
    #[inline(always)]
    pub fn ldolp(&self) -> LdolpR {
        LdolpR::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - Standby Mode"]
    #[inline(always)]
    pub fn stbmod(&self) -> StbmodR {
        StbmodR::new(((self.bits >> 1) & 1) != 0)
    }
    #[doc = "Bit 2 - Wakeup Flag Reset"]
    #[inline(always)]
    pub fn wurst(&self) -> WurstR {
        WurstR::new(((self.bits >> 2) & 1) != 0)
    }
    #[doc = "Bit 3 - Standby Flag Reset"]
    #[inline(always)]
    pub fn stbrst(&self) -> StbrstR {
        StbrstR::new(((self.bits >> 3) & 1) != 0)
    }
    #[doc = "Bit 4 - Low Voltage Detector Enable"]
    #[inline(always)]
    pub fn lvden(&self) -> LvdenR {
        LvdenR::new(((self.bits >> 4) & 1) != 0)
    }
    #[doc = "Bits 5:7 - Low Voltage Detector Threshold"]
    #[inline(always)]
    pub fn lvdt(&self) -> LvdtR {
        LvdtR::new(((self.bits >> 5) & 7) as u8)
    }
    #[doc = "Bit 8 - Backup Domain Write Enable"]
    #[inline(always)]
    pub fn bkpwen(&self) -> BkpwenR {
        BkpwenR::new(((self.bits >> 8) & 1) != 0)
    }
    #[doc = "Bit 10 - Low-driver mode when use low power LDO."]
    #[inline(always)]
    pub fn ldlp(&self) -> LdlpR {
        LdlpR::new(((self.bits >> 10) & 1) != 0)
    }
    #[doc = "Bit 11 - Low-driver mode when use normal power LDO"]
    #[inline(always)]
    pub fn ldnp(&self) -> LdnpR {
        LdnpR::new(((self.bits >> 11) & 1) != 0)
    }
    #[doc = "Bit 16 - High-driver mode enable"]
    #[inline(always)]
    pub fn hden(&self) -> HdenR {
        HdenR::new(((self.bits >> 16) & 1) != 0)
    }
    #[doc = "Bit 17 - High-driver mode switch"]
    #[inline(always)]
    pub fn hds(&self) -> HdsR {
        HdsR::new(((self.bits >> 17) & 1) != 0)
    }
    #[doc = "Bits 18:19 - Low-driver mode enable in Deep-sleep mode"]
    #[inline(always)]
    pub fn lden(&self) -> LdenR {
        LdenR::new(((self.bits >> 18) & 3) as u8)
    }
}
impl W {
    #[doc = "Bit 0 - LDO Low Power Mode"]
    #[inline(always)]
    #[must_use]
    pub fn ldolp(&mut self) -> LdolpW<Ctl0Spec> {
        LdolpW::new(self, 0)
    }
    #[doc = "Bit 1 - Standby Mode"]
    #[inline(always)]
    #[must_use]
    pub fn stbmod(&mut self) -> StbmodW<Ctl0Spec> {
        StbmodW::new(self, 1)
    }
    #[doc = "Bit 2 - Wakeup Flag Reset"]
    #[inline(always)]
    #[must_use]
    pub fn wurst(&mut self) -> WurstW<Ctl0Spec> {
        WurstW::new(self, 2)
    }
    #[doc = "Bit 3 - Standby Flag Reset"]
    #[inline(always)]
    #[must_use]
    pub fn stbrst(&mut self) -> StbrstW<Ctl0Spec> {
        StbrstW::new(self, 3)
    }
    #[doc = "Bit 4 - Low Voltage Detector Enable"]
    #[inline(always)]
    #[must_use]
    pub fn lvden(&mut self) -> LvdenW<Ctl0Spec> {
        LvdenW::new(self, 4)
    }
    #[doc = "Bits 5:7 - Low Voltage Detector Threshold"]
    #[inline(always)]
    #[must_use]
    pub fn lvdt(&mut self) -> LvdtW<Ctl0Spec> {
        LvdtW::new(self, 5)
    }
    #[doc = "Bit 8 - Backup Domain Write Enable"]
    #[inline(always)]
    #[must_use]
    pub fn bkpwen(&mut self) -> BkpwenW<Ctl0Spec> {
        BkpwenW::new(self, 8)
    }
    #[doc = "Bit 10 - Low-driver mode when use low power LDO."]
    #[inline(always)]
    #[must_use]
    pub fn ldlp(&mut self) -> LdlpW<Ctl0Spec> {
        LdlpW::new(self, 10)
    }
    #[doc = "Bit 11 - Low-driver mode when use normal power LDO"]
    #[inline(always)]
    #[must_use]
    pub fn ldnp(&mut self) -> LdnpW<Ctl0Spec> {
        LdnpW::new(self, 11)
    }
    #[doc = "Bit 16 - High-driver mode enable"]
    #[inline(always)]
    #[must_use]
    pub fn hden(&mut self) -> HdenW<Ctl0Spec> {
        HdenW::new(self, 16)
    }
    #[doc = "Bit 17 - High-driver mode switch"]
    #[inline(always)]
    #[must_use]
    pub fn hds(&mut self) -> HdsW<Ctl0Spec> {
        HdsW::new(self, 17)
    }
    #[doc = "Bits 18:19 - Low-driver mode enable in Deep-sleep mode"]
    #[inline(always)]
    #[must_use]
    pub fn lden(&mut self) -> LdenW<Ctl0Spec> {
        LdenW::new(self, 18)
    }
}
#[doc = "power control register 0\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`ctl0::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`ctl0::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct Ctl0Spec;
impl crate::RegisterSpec for Ctl0Spec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`ctl0::R`](R) reader structure"]
impl crate::Readable for Ctl0Spec {}
#[doc = "`write(|w| ..)` method takes [`ctl0::W`](W) writer structure"]
impl crate::Writable for Ctl0Spec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets CTL0 to value 0xc000"]
impl crate::Resettable for Ctl0Spec {
    const RESET_VALUE: u32 = 0xc000;
}
