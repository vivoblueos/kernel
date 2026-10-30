#[doc = "Register `WCMD` reader"]
pub type R = crate::R<WcmdSpec>;
#[doc = "Register `WCMD` writer"]
pub type W = crate::W<WcmdSpec>;
#[doc = "Field `SPI_WCMD` reader - SQPI write command for AHB write transfer"]
pub type SpiWcmdR = crate::FieldReader<u16>;
#[doc = "Field `SPI_WCMD` writer - SQPI write command for AHB write transfer"]
pub type SpiWcmdW<'a, REG> = crate::FieldWriter<'a, REG, 16, u16>;
#[doc = "Field `SQPI_WWAITCYCLE` reader - SQPI write command waitcycle number after address phase"]
pub type SqpiWwaitcycleR = crate::FieldReader;
#[doc = "Field `SQPI_WWAITCYCLE` writer - SQPI write command waitcycle number after address phase"]
pub type SqpiWwaitcycleW<'a, REG> = crate::FieldWriter<'a, REG, 4>;
#[doc = "Field `SQPI_WMODE` reader - SQPI controller write command mode"]
pub type SqpiWmodeR = crate::FieldReader;
#[doc = "Field `SQPI_WMODE` writer - SQPI controller write command mode"]
pub type SqpiWmodeW<'a, REG> = crate::FieldWriter<'a, REG, 3>;
#[doc = "Field `SQPI_SC` reader - Send special command"]
pub type SqpiScR = crate::BitReader;
#[doc = "Field `SQPI_SC` writer - Send special command"]
pub type SqpiScW<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bits 0:15 - SQPI write command for AHB write transfer"]
    #[inline(always)]
    pub fn spi_wcmd(&self) -> SpiWcmdR {
        SpiWcmdR::new((self.bits & 0xffff) as u16)
    }
    #[doc = "Bits 16:19 - SQPI write command waitcycle number after address phase"]
    #[inline(always)]
    pub fn sqpi_wwaitcycle(&self) -> SqpiWwaitcycleR {
        SqpiWwaitcycleR::new(((self.bits >> 16) & 0x0f) as u8)
    }
    #[doc = "Bits 20:22 - SQPI controller write command mode"]
    #[inline(always)]
    pub fn sqpi_wmode(&self) -> SqpiWmodeR {
        SqpiWmodeR::new(((self.bits >> 20) & 7) as u8)
    }
    #[doc = "Bit 31 - Send special command"]
    #[inline(always)]
    pub fn sqpi_sc(&self) -> SqpiScR {
        SqpiScR::new(((self.bits >> 31) & 1) != 0)
    }
}
impl W {
    #[doc = "Bits 0:15 - SQPI write command for AHB write transfer"]
    #[inline(always)]
    #[must_use]
    pub fn spi_wcmd(&mut self) -> SpiWcmdW<WcmdSpec> {
        SpiWcmdW::new(self, 0)
    }
    #[doc = "Bits 16:19 - SQPI write command waitcycle number after address phase"]
    #[inline(always)]
    #[must_use]
    pub fn sqpi_wwaitcycle(&mut self) -> SqpiWwaitcycleW<WcmdSpec> {
        SqpiWwaitcycleW::new(self, 16)
    }
    #[doc = "Bits 20:22 - SQPI controller write command mode"]
    #[inline(always)]
    #[must_use]
    pub fn sqpi_wmode(&mut self) -> SqpiWmodeW<WcmdSpec> {
        SqpiWmodeW::new(self, 20)
    }
    #[doc = "Bit 31 - Send special command"]
    #[inline(always)]
    #[must_use]
    pub fn sqpi_sc(&mut self) -> SqpiScW<WcmdSpec> {
        SqpiScW::new(self, 31)
    }
}
#[doc = "Write Command Register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`wcmd::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`wcmd::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct WcmdSpec;
impl crate::RegisterSpec for WcmdSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`wcmd::R`](R) reader structure"]
impl crate::Readable for WcmdSpec {}
#[doc = "`write(|w| ..)` method takes [`wcmd::W`](W) writer structure"]
impl crate::Writable for WcmdSpec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets WCMD to value 0x0001_0000"]
impl crate::Resettable for WcmdSpec {
    const RESET_VALUE: u32 = 0x0001_0000;
}
