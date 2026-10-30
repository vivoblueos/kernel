#[doc = "Register `CTL0` reader"]
pub type R = crate::R<Ctl0Spec>;
#[doc = "Register `CTL0` writer"]
pub type W = crate::W<Ctl0Spec>;
#[doc = "Field `I2CEN` reader - I2C peripheral enable"]
pub type I2cenR = crate::BitReader;
#[doc = "Field `I2CEN` writer - I2C peripheral enable"]
pub type I2cenW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SMBEN` reader - SMBus/I2C mode switch"]
pub type SmbenR = crate::BitReader;
#[doc = "Field `SMBEN` writer - SMBus/I2C mode switch"]
pub type SmbenW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SMBSEL` reader - SMBusType Selection"]
pub type SmbselR = crate::BitReader;
#[doc = "Field `SMBSEL` writer - SMBusType Selection"]
pub type SmbselW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ARPEN` reader - ARP protocol in SMBus switch"]
pub type ArpenR = crate::BitReader;
#[doc = "Field `ARPEN` writer - ARP protocol in SMBus switch"]
pub type ArpenW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `PECEN` reader - PEC Calculation Switch"]
pub type PecenR = crate::BitReader;
#[doc = "Field `PECEN` writer - PEC Calculation Switch"]
pub type PecenW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `GCEN` reader - Whether or not to response to a General Call (0x00)"]
pub type GcenR = crate::BitReader;
#[doc = "Field `GCEN` writer - Whether or not to response to a General Call (0x00)"]
pub type GcenW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SS` reader - Whether to stretch SCL low when data is not ready in slave mode"]
pub type SsR = crate::BitReader;
#[doc = "Field `SS` writer - Whether to stretch SCL low when data is not ready in slave mode"]
pub type SsW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `START` reader - Generate a START condition on I2C bus"]
pub type StartR = crate::BitReader;
#[doc = "Field `START` writer - Generate a START condition on I2C bus"]
pub type StartW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `STOP` reader - Generate a STOP condition on I2C bus"]
pub type StopR = crate::BitReader;
#[doc = "Field `STOP` writer - Generate a STOP condition on I2C bus"]
pub type StopW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ACKEN` reader - Whether or not to send an ACK"]
pub type AckenR = crate::BitReader;
#[doc = "Field `ACKEN` writer - Whether or not to send an ACK"]
pub type AckenW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `POAP` reader - Position of ACK and PEC when receiving"]
pub type PoapR = crate::BitReader;
#[doc = "Field `POAP` writer - Position of ACK and PEC when receiving"]
pub type PoapW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `PECTRANS` reader - PEC Transfer"]
pub type PectransR = crate::BitReader;
#[doc = "Field `PECTRANS` writer - PEC Transfer"]
pub type PectransW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SALT` reader - SMBus alert"]
pub type SaltR = crate::BitReader;
#[doc = "Field `SALT` writer - SMBus alert"]
pub type SaltW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SRESET` reader - Software reset"]
pub type SresetR = crate::BitReader;
#[doc = "Field `SRESET` writer - Software reset"]
pub type SresetW<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 0 - I2C peripheral enable"]
    #[inline(always)]
    pub fn i2cen(&self) -> I2cenR {
        I2cenR::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - SMBus/I2C mode switch"]
    #[inline(always)]
    pub fn smben(&self) -> SmbenR {
        SmbenR::new(((self.bits >> 1) & 1) != 0)
    }
    #[doc = "Bit 3 - SMBusType Selection"]
    #[inline(always)]
    pub fn smbsel(&self) -> SmbselR {
        SmbselR::new(((self.bits >> 3) & 1) != 0)
    }
    #[doc = "Bit 4 - ARP protocol in SMBus switch"]
    #[inline(always)]
    pub fn arpen(&self) -> ArpenR {
        ArpenR::new(((self.bits >> 4) & 1) != 0)
    }
    #[doc = "Bit 5 - PEC Calculation Switch"]
    #[inline(always)]
    pub fn pecen(&self) -> PecenR {
        PecenR::new(((self.bits >> 5) & 1) != 0)
    }
    #[doc = "Bit 6 - Whether or not to response to a General Call (0x00)"]
    #[inline(always)]
    pub fn gcen(&self) -> GcenR {
        GcenR::new(((self.bits >> 6) & 1) != 0)
    }
    #[doc = "Bit 7 - Whether to stretch SCL low when data is not ready in slave mode"]
    #[inline(always)]
    pub fn ss(&self) -> SsR {
        SsR::new(((self.bits >> 7) & 1) != 0)
    }
    #[doc = "Bit 8 - Generate a START condition on I2C bus"]
    #[inline(always)]
    pub fn start(&self) -> StartR {
        StartR::new(((self.bits >> 8) & 1) != 0)
    }
    #[doc = "Bit 9 - Generate a STOP condition on I2C bus"]
    #[inline(always)]
    pub fn stop(&self) -> StopR {
        StopR::new(((self.bits >> 9) & 1) != 0)
    }
    #[doc = "Bit 10 - Whether or not to send an ACK"]
    #[inline(always)]
    pub fn acken(&self) -> AckenR {
        AckenR::new(((self.bits >> 10) & 1) != 0)
    }
    #[doc = "Bit 11 - Position of ACK and PEC when receiving"]
    #[inline(always)]
    pub fn poap(&self) -> PoapR {
        PoapR::new(((self.bits >> 11) & 1) != 0)
    }
    #[doc = "Bit 12 - PEC Transfer"]
    #[inline(always)]
    pub fn pectrans(&self) -> PectransR {
        PectransR::new(((self.bits >> 12) & 1) != 0)
    }
    #[doc = "Bit 13 - SMBus alert"]
    #[inline(always)]
    pub fn salt(&self) -> SaltR {
        SaltR::new(((self.bits >> 13) & 1) != 0)
    }
    #[doc = "Bit 15 - Software reset"]
    #[inline(always)]
    pub fn sreset(&self) -> SresetR {
        SresetR::new(((self.bits >> 15) & 1) != 0)
    }
}
impl W {
    #[doc = "Bit 0 - I2C peripheral enable"]
    #[inline(always)]
    #[must_use]
    pub fn i2cen(&mut self) -> I2cenW<Ctl0Spec> {
        I2cenW::new(self, 0)
    }
    #[doc = "Bit 1 - SMBus/I2C mode switch"]
    #[inline(always)]
    #[must_use]
    pub fn smben(&mut self) -> SmbenW<Ctl0Spec> {
        SmbenW::new(self, 1)
    }
    #[doc = "Bit 3 - SMBusType Selection"]
    #[inline(always)]
    #[must_use]
    pub fn smbsel(&mut self) -> SmbselW<Ctl0Spec> {
        SmbselW::new(self, 3)
    }
    #[doc = "Bit 4 - ARP protocol in SMBus switch"]
    #[inline(always)]
    #[must_use]
    pub fn arpen(&mut self) -> ArpenW<Ctl0Spec> {
        ArpenW::new(self, 4)
    }
    #[doc = "Bit 5 - PEC Calculation Switch"]
    #[inline(always)]
    #[must_use]
    pub fn pecen(&mut self) -> PecenW<Ctl0Spec> {
        PecenW::new(self, 5)
    }
    #[doc = "Bit 6 - Whether or not to response to a General Call (0x00)"]
    #[inline(always)]
    #[must_use]
    pub fn gcen(&mut self) -> GcenW<Ctl0Spec> {
        GcenW::new(self, 6)
    }
    #[doc = "Bit 7 - Whether to stretch SCL low when data is not ready in slave mode"]
    #[inline(always)]
    #[must_use]
    pub fn ss(&mut self) -> SsW<Ctl0Spec> {
        SsW::new(self, 7)
    }
    #[doc = "Bit 8 - Generate a START condition on I2C bus"]
    #[inline(always)]
    #[must_use]
    pub fn start(&mut self) -> StartW<Ctl0Spec> {
        StartW::new(self, 8)
    }
    #[doc = "Bit 9 - Generate a STOP condition on I2C bus"]
    #[inline(always)]
    #[must_use]
    pub fn stop(&mut self) -> StopW<Ctl0Spec> {
        StopW::new(self, 9)
    }
    #[doc = "Bit 10 - Whether or not to send an ACK"]
    #[inline(always)]
    #[must_use]
    pub fn acken(&mut self) -> AckenW<Ctl0Spec> {
        AckenW::new(self, 10)
    }
    #[doc = "Bit 11 - Position of ACK and PEC when receiving"]
    #[inline(always)]
    #[must_use]
    pub fn poap(&mut self) -> PoapW<Ctl0Spec> {
        PoapW::new(self, 11)
    }
    #[doc = "Bit 12 - PEC Transfer"]
    #[inline(always)]
    #[must_use]
    pub fn pectrans(&mut self) -> PectransW<Ctl0Spec> {
        PectransW::new(self, 12)
    }
    #[doc = "Bit 13 - SMBus alert"]
    #[inline(always)]
    #[must_use]
    pub fn salt(&mut self) -> SaltW<Ctl0Spec> {
        SaltW::new(self, 13)
    }
    #[doc = "Bit 15 - Software reset"]
    #[inline(always)]
    #[must_use]
    pub fn sreset(&mut self) -> SresetW<Ctl0Spec> {
        SresetW::new(self, 15)
    }
}
#[doc = "Control register 0\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`ctl0::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`ctl0::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
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
#[doc = "`reset()` method sets CTL0 to value 0"]
impl crate::Resettable for Ctl0Spec {
    const RESET_VALUE: u32 = 0;
}
