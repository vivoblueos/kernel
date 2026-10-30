#[doc = "Register `RCMD` reader"]
pub type R = crate::R<RcmdSpec>;
#[doc = "Register `RCMD` writer"]
pub type W = crate::W<RcmdSpec>;
#[doc = "Field `SQPI_RCMD` reader - SQPI read command for AHB read transfer"]
pub type SqpiRcmdR = crate::FieldReader<u16>;
#[doc = "Field `SQPI_RCMD` writer - SQPI read command for AHB read transfer"]
pub type SqpiRcmdW<'a, REG> = crate::FieldWriter<'a, REG, 16, u16>;
#[doc = "Field `SQPI_RWAITCYCLE` reader - SQPI read command waitcycle number after address phase"]
pub type SqpiRwaitcycleR = crate::FieldReader;
#[doc = "Field `SQPI_RWAITCYCLE` writer - SQPI read command waitcycle number after address phase"]
pub type SqpiRwaitcycleW<'a, REG> = crate::FieldWriter<'a, REG, 4>;
#[doc = "Field `SQPI_RMODE` reader - SQPI controller read command mode"]
pub type SqpiRmodeR = crate::FieldReader;
#[doc = "Field `SQPI_RMODE` writer - SQPI controller read command mode"]
pub type SqpiRmodeW<'a, REG> = crate::FieldWriter<'a, REG, 3>;
#[doc = "Field `SQPI_RID` reader - Send read ID command"]
pub type SqpiRidR = crate::BitReader;
#[doc = "Field `SQPI_RID` writer - Send read ID command"]
pub type SqpiRidW<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bits 0:15 - SQPI read command for AHB read transfer"]
    #[inline(always)]
    pub fn sqpi_rcmd(&self) -> SqpiRcmdR {
        SqpiRcmdR::new((self.bits & 0xffff) as u16)
    }
    #[doc = "Bits 16:19 - SQPI read command waitcycle number after address phase"]
    #[inline(always)]
    pub fn sqpi_rwaitcycle(&self) -> SqpiRwaitcycleR {
        SqpiRwaitcycleR::new(((self.bits >> 16) & 0x0f) as u8)
    }
    #[doc = "Bits 20:22 - SQPI controller read command mode"]
    #[inline(always)]
    pub fn sqpi_rmode(&self) -> SqpiRmodeR {
        SqpiRmodeR::new(((self.bits >> 20) & 7) as u8)
    }
    #[doc = "Bit 31 - Send read ID command"]
    #[inline(always)]
    pub fn sqpi_rid(&self) -> SqpiRidR {
        SqpiRidR::new(((self.bits >> 31) & 1) != 0)
    }
}
impl W {
    #[doc = "Bits 0:15 - SQPI read command for AHB read transfer"]
    #[inline(always)]
    #[must_use]
    pub fn sqpi_rcmd(&mut self) -> SqpiRcmdW<RcmdSpec> {
        SqpiRcmdW::new(self, 0)
    }
    #[doc = "Bits 16:19 - SQPI read command waitcycle number after address phase"]
    #[inline(always)]
    #[must_use]
    pub fn sqpi_rwaitcycle(&mut self) -> SqpiRwaitcycleW<RcmdSpec> {
        SqpiRwaitcycleW::new(self, 16)
    }
    #[doc = "Bits 20:22 - SQPI controller read command mode"]
    #[inline(always)]
    #[must_use]
    pub fn sqpi_rmode(&mut self) -> SqpiRmodeW<RcmdSpec> {
        SqpiRmodeW::new(self, 20)
    }
    #[doc = "Bit 31 - Send read ID command"]
    #[inline(always)]
    #[must_use]
    pub fn sqpi_rid(&mut self) -> SqpiRidW<RcmdSpec> {
        SqpiRidW::new(self, 31)
    }
}
#[doc = "SQPI Read Command Register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`rcmd::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`rcmd::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct RcmdSpec;
impl crate::RegisterSpec for RcmdSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`rcmd::R`](R) reader structure"]
impl crate::Readable for RcmdSpec {}
#[doc = "`write(|w| ..)` method takes [`rcmd::W`](W) writer structure"]
impl crate::Writable for RcmdSpec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets RCMD to value 0x0010_0000"]
impl crate::Resettable for RcmdSpec {
    const RESET_VALUE: u32 = 0x0010_0000;
}
