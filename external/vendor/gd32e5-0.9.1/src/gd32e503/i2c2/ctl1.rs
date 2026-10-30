#[doc = "Register `CTL1` reader"]
pub type R = crate::R<Ctl1Spec>;
#[doc = "Register `CTL1` writer"]
pub type W = crate::W<Ctl1Spec>;
#[doc = "Field `SADDRESS` reader - Slave address to be sent"]
pub type SaddressR = crate::FieldReader<u16>;
#[doc = "Field `SADDRESS` writer - Slave address to be sent"]
pub type SaddressW<'a, REG> = crate::FieldWriter<'a, REG, 10, u16>;
#[doc = "Field `TRDIR` reader - Transfer direction in master mode"]
pub type TrdirR = crate::BitReader;
#[doc = "Field `TRDIR` writer - Transfer direction in master mode"]
pub type TrdirW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ADD10EN` reader - 10-bit addressing mode enable in master mode"]
pub type Add10enR = crate::BitReader;
#[doc = "Field `ADD10EN` writer - 10-bit addressing mode enable in master mode"]
pub type Add10enW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `HEAD10R` reader - 10-bit address header executes read direction only in master receive mode"]
pub type Head10rR = crate::BitReader;
#[doc = "Field `HEAD10R` writer - 10-bit address header executes read direction only in master receive mode"]
pub type Head10rW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `START` reader - Generate a START condition on I2C bus"]
pub type StartR = crate::BitReader;
#[doc = "Field `START` writer - Generate a START condition on I2C bus"]
pub type StartW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `STOP` reader - Generate a STOP condition on I2C bus"]
pub type StopR = crate::BitReader;
#[doc = "Field `STOP` writer - Generate a STOP condition on I2C bus"]
pub type StopW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `NACKEN` reader - Generate NACK in slave mode"]
pub type NackenR = crate::BitReader;
#[doc = "Field `NACKEN` writer - Generate NACK in slave mode"]
pub type NackenW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `BYTENUM` reader - Number of bytes to be transferred"]
pub type BytenumR = crate::FieldReader;
#[doc = "Field `BYTENUM` writer - Number of bytes to be transferred"]
pub type BytenumW<'a, REG> = crate::FieldWriter<'a, REG, 8>;
#[doc = "Field `RELOAD` reader - Reload mode"]
pub type ReloadR = crate::BitReader;
#[doc = "Field `RELOAD` writer - Reload mode"]
pub type ReloadW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `AUTOEND` reader - Automatic end mode in master mode"]
pub type AutoendR = crate::BitReader;
#[doc = "Field `AUTOEND` writer - Automatic end mode in master mode"]
pub type AutoendW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `PECTRANS` reader - PEC Transfer"]
pub type PectransR = crate::BitReader;
#[doc = "Field `PECTRANS` writer - PEC Transfer"]
pub type PectransW<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bits 0:9 - Slave address to be sent"]
    #[inline(always)]
    pub fn saddress(&self) -> SaddressR {
        SaddressR::new((self.bits & 0x03ff) as u16)
    }
    #[doc = "Bit 10 - Transfer direction in master mode"]
    #[inline(always)]
    pub fn trdir(&self) -> TrdirR {
        TrdirR::new(((self.bits >> 10) & 1) != 0)
    }
    #[doc = "Bit 11 - 10-bit addressing mode enable in master mode"]
    #[inline(always)]
    pub fn add10en(&self) -> Add10enR {
        Add10enR::new(((self.bits >> 11) & 1) != 0)
    }
    #[doc = "Bit 12 - 10-bit address header executes read direction only in master receive mode"]
    #[inline(always)]
    pub fn head10r(&self) -> Head10rR {
        Head10rR::new(((self.bits >> 12) & 1) != 0)
    }
    #[doc = "Bit 13 - Generate a START condition on I2C bus"]
    #[inline(always)]
    pub fn start(&self) -> StartR {
        StartR::new(((self.bits >> 13) & 1) != 0)
    }
    #[doc = "Bit 14 - Generate a STOP condition on I2C bus"]
    #[inline(always)]
    pub fn stop(&self) -> StopR {
        StopR::new(((self.bits >> 14) & 1) != 0)
    }
    #[doc = "Bit 15 - Generate NACK in slave mode"]
    #[inline(always)]
    pub fn nacken(&self) -> NackenR {
        NackenR::new(((self.bits >> 15) & 1) != 0)
    }
    #[doc = "Bits 16:23 - Number of bytes to be transferred"]
    #[inline(always)]
    pub fn bytenum(&self) -> BytenumR {
        BytenumR::new(((self.bits >> 16) & 0xff) as u8)
    }
    #[doc = "Bit 24 - Reload mode"]
    #[inline(always)]
    pub fn reload(&self) -> ReloadR {
        ReloadR::new(((self.bits >> 24) & 1) != 0)
    }
    #[doc = "Bit 25 - Automatic end mode in master mode"]
    #[inline(always)]
    pub fn autoend(&self) -> AutoendR {
        AutoendR::new(((self.bits >> 25) & 1) != 0)
    }
    #[doc = "Bit 26 - PEC Transfer"]
    #[inline(always)]
    pub fn pectrans(&self) -> PectransR {
        PectransR::new(((self.bits >> 26) & 1) != 0)
    }
}
impl W {
    #[doc = "Bits 0:9 - Slave address to be sent"]
    #[inline(always)]
    #[must_use]
    pub fn saddress(&mut self) -> SaddressW<Ctl1Spec> {
        SaddressW::new(self, 0)
    }
    #[doc = "Bit 10 - Transfer direction in master mode"]
    #[inline(always)]
    #[must_use]
    pub fn trdir(&mut self) -> TrdirW<Ctl1Spec> {
        TrdirW::new(self, 10)
    }
    #[doc = "Bit 11 - 10-bit addressing mode enable in master mode"]
    #[inline(always)]
    #[must_use]
    pub fn add10en(&mut self) -> Add10enW<Ctl1Spec> {
        Add10enW::new(self, 11)
    }
    #[doc = "Bit 12 - 10-bit address header executes read direction only in master receive mode"]
    #[inline(always)]
    #[must_use]
    pub fn head10r(&mut self) -> Head10rW<Ctl1Spec> {
        Head10rW::new(self, 12)
    }
    #[doc = "Bit 13 - Generate a START condition on I2C bus"]
    #[inline(always)]
    #[must_use]
    pub fn start(&mut self) -> StartW<Ctl1Spec> {
        StartW::new(self, 13)
    }
    #[doc = "Bit 14 - Generate a STOP condition on I2C bus"]
    #[inline(always)]
    #[must_use]
    pub fn stop(&mut self) -> StopW<Ctl1Spec> {
        StopW::new(self, 14)
    }
    #[doc = "Bit 15 - Generate NACK in slave mode"]
    #[inline(always)]
    #[must_use]
    pub fn nacken(&mut self) -> NackenW<Ctl1Spec> {
        NackenW::new(self, 15)
    }
    #[doc = "Bits 16:23 - Number of bytes to be transferred"]
    #[inline(always)]
    #[must_use]
    pub fn bytenum(&mut self) -> BytenumW<Ctl1Spec> {
        BytenumW::new(self, 16)
    }
    #[doc = "Bit 24 - Reload mode"]
    #[inline(always)]
    #[must_use]
    pub fn reload(&mut self) -> ReloadW<Ctl1Spec> {
        ReloadW::new(self, 24)
    }
    #[doc = "Bit 25 - Automatic end mode in master mode"]
    #[inline(always)]
    #[must_use]
    pub fn autoend(&mut self) -> AutoendW<Ctl1Spec> {
        AutoendW::new(self, 25)
    }
    #[doc = "Bit 26 - PEC Transfer"]
    #[inline(always)]
    #[must_use]
    pub fn pectrans(&mut self) -> PectransW<Ctl1Spec> {
        PectransW::new(self, 26)
    }
}
#[doc = "Control register 1\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`ctl1::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`ctl1::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct Ctl1Spec;
impl crate::RegisterSpec for Ctl1Spec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`ctl1::R`](R) reader structure"]
impl crate::Readable for Ctl1Spec {}
#[doc = "`write(|w| ..)` method takes [`ctl1::W`](W) writer structure"]
impl crate::Writable for Ctl1Spec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets CTL1 to value 0"]
impl crate::Resettable for Ctl1Spec {
    const RESET_VALUE: u32 = 0;
}
