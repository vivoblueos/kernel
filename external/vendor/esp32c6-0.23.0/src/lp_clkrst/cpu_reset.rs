#[doc = "Register `CPU_RESET` reader"]
pub type R = crate::R<CPU_RESET_SPEC>;
#[doc = "Register `CPU_RESET` writer"]
pub type W = crate::W<CPU_RESET_SPEC>;
#[doc = "Field `RTC_WDT_CPU_RESET_LENGTH` reader - need_des"]
pub type RTC_WDT_CPU_RESET_LENGTH_R = crate::FieldReader;
#[doc = "Field `RTC_WDT_CPU_RESET_LENGTH` writer - need_des"]
pub type RTC_WDT_CPU_RESET_LENGTH_W<'a, REG> = crate::FieldWriter<'a, REG, 3>;
#[doc = "Field `RTC_WDT_CPU_RESET_EN` reader - need_des"]
pub type RTC_WDT_CPU_RESET_EN_R = crate::BitReader;
#[doc = "Field `RTC_WDT_CPU_RESET_EN` writer - need_des"]
pub type RTC_WDT_CPU_RESET_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `CPU_STALL_WAIT` reader - need_des"]
pub type CPU_STALL_WAIT_R = crate::FieldReader;
#[doc = "Field `CPU_STALL_WAIT` writer - need_des"]
pub type CPU_STALL_WAIT_W<'a, REG> = crate::FieldWriter<'a, REG, 5>;
#[doc = "Field `CPU_STALL_EN` reader - need_des"]
pub type CPU_STALL_EN_R = crate::BitReader;
#[doc = "Field `CPU_STALL_EN` writer - need_des"]
pub type CPU_STALL_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bits 22:24 - need_des"]
    #[inline(always)]
    pub fn rtc_wdt_cpu_reset_length(&self) -> RTC_WDT_CPU_RESET_LENGTH_R {
        RTC_WDT_CPU_RESET_LENGTH_R::new(((self.bits >> 22) & 7) as u8)
    }
    #[doc = "Bit 25 - need_des"]
    #[inline(always)]
    pub fn rtc_wdt_cpu_reset_en(&self) -> RTC_WDT_CPU_RESET_EN_R {
        RTC_WDT_CPU_RESET_EN_R::new(((self.bits >> 25) & 1) != 0)
    }
    #[doc = "Bits 26:30 - need_des"]
    #[inline(always)]
    pub fn cpu_stall_wait(&self) -> CPU_STALL_WAIT_R {
        CPU_STALL_WAIT_R::new(((self.bits >> 26) & 0x1f) as u8)
    }
    #[doc = "Bit 31 - need_des"]
    #[inline(always)]
    pub fn cpu_stall_en(&self) -> CPU_STALL_EN_R {
        CPU_STALL_EN_R::new(((self.bits >> 31) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("CPU_RESET")
            .field("rtc_wdt_cpu_reset_length", &self.rtc_wdt_cpu_reset_length())
            .field("rtc_wdt_cpu_reset_en", &self.rtc_wdt_cpu_reset_en())
            .field("cpu_stall_wait", &self.cpu_stall_wait())
            .field("cpu_stall_en", &self.cpu_stall_en())
            .finish()
    }
}
impl W {
    #[doc = "Bits 22:24 - need_des"]
    #[inline(always)]
    pub fn rtc_wdt_cpu_reset_length(&mut self) -> RTC_WDT_CPU_RESET_LENGTH_W<'_, CPU_RESET_SPEC> {
        RTC_WDT_CPU_RESET_LENGTH_W::new(self, 22)
    }
    #[doc = "Bit 25 - need_des"]
    #[inline(always)]
    pub fn rtc_wdt_cpu_reset_en(&mut self) -> RTC_WDT_CPU_RESET_EN_W<'_, CPU_RESET_SPEC> {
        RTC_WDT_CPU_RESET_EN_W::new(self, 25)
    }
    #[doc = "Bits 26:30 - need_des"]
    #[inline(always)]
    pub fn cpu_stall_wait(&mut self) -> CPU_STALL_WAIT_W<'_, CPU_RESET_SPEC> {
        CPU_STALL_WAIT_W::new(self, 26)
    }
    #[doc = "Bit 31 - need_des"]
    #[inline(always)]
    pub fn cpu_stall_en(&mut self) -> CPU_STALL_EN_W<'_, CPU_RESET_SPEC> {
        CPU_STALL_EN_W::new(self, 31)
    }
}
#[doc = "need_des\n\nYou can [`read`](crate::Reg::read) this register and get [`cpu_reset::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`cpu_reset::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct CPU_RESET_SPEC;
impl crate::RegisterSpec for CPU_RESET_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`cpu_reset::R`](R) reader structure"]
impl crate::Readable for CPU_RESET_SPEC {}
#[doc = "`write(|w| ..)` method takes [`cpu_reset::W`](W) writer structure"]
impl crate::Writable for CPU_RESET_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets CPU_RESET to value 0x0440_0000"]
impl crate::Resettable for CPU_RESET_SPEC {
    const RESET_VALUE: u32 = 0x0440_0000;
}
