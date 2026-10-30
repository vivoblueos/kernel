#[doc = "Register `INIT` reader"]
pub type R = crate::R<InitSpec>;
#[doc = "Register `INIT` writer"]
pub type W = crate::W<InitSpec>;
#[doc = "Field `SQPI_CMDBIT` reader - Bit number of SQPI controller command phase"]
pub type SqpiCmdbitR = crate::FieldReader;
#[doc = "Field `SQPI_CMDBIT` writer - Bit number of SQPI controller command phase"]
pub type SqpiCmdbitW<'a, REG> = crate::FieldWriter<'a, REG, 2>;
#[doc = "Field `SQPI_CLKDIV` reader - Clock divider for SQPI output clock"]
pub type SqpiClkdivR = crate::FieldReader;
#[doc = "Field `SQPI_CLKDIV` writer - Clock divider for SQPI output clock"]
pub type SqpiClkdivW<'a, REG> = crate::FieldWriter<'a, REG, 6>;
#[doc = "Field `SQPI_ADDRBIT` reader - Bit number of SPI PSRAM address phase."]
pub type SqpiAddrbitR = crate::FieldReader;
#[doc = "Field `SQPI_ADDRBIT` writer - Bit number of SPI PSRAM address phase."]
pub type SqpiAddrbitW<'a, REG> = crate::FieldWriter<'a, REG, 5>;
#[doc = "Field `SQPI_IDLEN` reader - SQPI controller external memory ID length"]
pub type SqpiIdlenR = crate::FieldReader;
#[doc = "Field `SQPI_IDLEN` writer - SQPI controller external memory ID length"]
pub type SqpiIdlenW<'a, REG> = crate::FieldWriter<'a, REG, 2>;
#[doc = "Field `SQPI_PL` reader - Read data sample polarity."]
pub type SqpiPlR = crate::BitReader;
#[doc = "Field `SQPI_PL` writer - Read data sample polarity."]
pub type SqpiPlW<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bits 16:17 - Bit number of SQPI controller command phase"]
    #[inline(always)]
    pub fn sqpi_cmdbit(&self) -> SqpiCmdbitR {
        SqpiCmdbitR::new(((self.bits >> 16) & 3) as u8)
    }
    #[doc = "Bits 18:23 - Clock divider for SQPI output clock"]
    #[inline(always)]
    pub fn sqpi_clkdiv(&self) -> SqpiClkdivR {
        SqpiClkdivR::new(((self.bits >> 18) & 0x3f) as u8)
    }
    #[doc = "Bits 24:28 - Bit number of SPI PSRAM address phase."]
    #[inline(always)]
    pub fn sqpi_addrbit(&self) -> SqpiAddrbitR {
        SqpiAddrbitR::new(((self.bits >> 24) & 0x1f) as u8)
    }
    #[doc = "Bits 29:30 - SQPI controller external memory ID length"]
    #[inline(always)]
    pub fn sqpi_idlen(&self) -> SqpiIdlenR {
        SqpiIdlenR::new(((self.bits >> 29) & 3) as u8)
    }
    #[doc = "Bit 31 - Read data sample polarity."]
    #[inline(always)]
    pub fn sqpi_pl(&self) -> SqpiPlR {
        SqpiPlR::new(((self.bits >> 31) & 1) != 0)
    }
}
impl W {
    #[doc = "Bits 16:17 - Bit number of SQPI controller command phase"]
    #[inline(always)]
    #[must_use]
    pub fn sqpi_cmdbit(&mut self) -> SqpiCmdbitW<InitSpec> {
        SqpiCmdbitW::new(self, 16)
    }
    #[doc = "Bits 18:23 - Clock divider for SQPI output clock"]
    #[inline(always)]
    #[must_use]
    pub fn sqpi_clkdiv(&mut self) -> SqpiClkdivW<InitSpec> {
        SqpiClkdivW::new(self, 18)
    }
    #[doc = "Bits 24:28 - Bit number of SPI PSRAM address phase."]
    #[inline(always)]
    #[must_use]
    pub fn sqpi_addrbit(&mut self) -> SqpiAddrbitW<InitSpec> {
        SqpiAddrbitW::new(self, 24)
    }
    #[doc = "Bits 29:30 - SQPI controller external memory ID length"]
    #[inline(always)]
    #[must_use]
    pub fn sqpi_idlen(&mut self) -> SqpiIdlenW<InitSpec> {
        SqpiIdlenW::new(self, 29)
    }
    #[doc = "Bit 31 - Read data sample polarity."]
    #[inline(always)]
    #[must_use]
    pub fn sqpi_pl(&mut self) -> SqpiPlW<InitSpec> {
        SqpiPlW::new(self, 31)
    }
}
#[doc = "SQPI Initial Register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`init::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`init::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct InitSpec;
impl crate::RegisterSpec for InitSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`init::R`](R) reader structure"]
impl crate::Readable for InitSpec {}
#[doc = "`write(|w| ..)` method takes [`init::W`](W) writer structure"]
impl crate::Writable for InitSpec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets INIT to value 0x1801_0004"]
impl crate::Resettable for InitSpec {
    const RESET_VALUE: u32 = 0x1801_0004;
}
