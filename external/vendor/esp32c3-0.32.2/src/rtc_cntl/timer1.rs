#[doc = "Register `TIMER1` reader"]
pub type R = crate::R<TIMER1_SPEC>;
#[doc = "Register `TIMER1` writer"]
pub type W = crate::W<TIMER1_SPEC>;
#[doc = "Field `CPU_STALL_EN` reader - CPU stall enable bit"]
pub type CPU_STALL_EN_R = crate::BitReader;
#[doc = "Field `CPU_STALL_EN` writer - CPU stall enable bit"]
pub type CPU_STALL_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `CPU_STALL_WAIT` reader - CPU stall wait cycles in fast_clk_rtc"]
pub type CPU_STALL_WAIT_R = crate::FieldReader;
#[doc = "Field `CPU_STALL_WAIT` writer - CPU stall wait cycles in fast_clk_rtc"]
pub type CPU_STALL_WAIT_W<'a, REG> = crate::FieldWriter<'a, REG, 5>;
#[doc = "Field `CK8M_WAIT` reader - CK8M wait cycles in slow_clk_rtc"]
pub type CK8M_WAIT_R = crate::FieldReader;
#[doc = "Field `CK8M_WAIT` writer - CK8M wait cycles in slow_clk_rtc"]
pub type CK8M_WAIT_W<'a, REG> = crate::FieldWriter<'a, REG, 8>;
#[doc = "Field `XTL_BUF_WAIT` reader - XTAL wait cycles in slow_clk_rtc"]
pub type XTL_BUF_WAIT_R = crate::FieldReader<u16>;
#[doc = "Field `XTL_BUF_WAIT` writer - XTAL wait cycles in slow_clk_rtc"]
pub type XTL_BUF_WAIT_W<'a, REG> = crate::FieldWriter<'a, REG, 10, u16>;
#[doc = "Field `PLL_BUF_WAIT` reader - PLL wait cycles in slow_clk_rtc"]
pub type PLL_BUF_WAIT_R = crate::FieldReader;
#[doc = "Field `PLL_BUF_WAIT` writer - PLL wait cycles in slow_clk_rtc"]
pub type PLL_BUF_WAIT_W<'a, REG> = crate::FieldWriter<'a, REG, 8>;
impl R {
    #[doc = "Bit 0 - CPU stall enable bit"]
    #[inline(always)]
    pub fn cpu_stall_en(&self) -> CPU_STALL_EN_R {
        CPU_STALL_EN_R::new((self.bits & 1) != 0)
    }
    #[doc = "Bits 1:5 - CPU stall wait cycles in fast_clk_rtc"]
    #[inline(always)]
    pub fn cpu_stall_wait(&self) -> CPU_STALL_WAIT_R {
        CPU_STALL_WAIT_R::new(((self.bits >> 1) & 0x1f) as u8)
    }
    #[doc = "Bits 6:13 - CK8M wait cycles in slow_clk_rtc"]
    #[inline(always)]
    pub fn ck8m_wait(&self) -> CK8M_WAIT_R {
        CK8M_WAIT_R::new(((self.bits >> 6) & 0xff) as u8)
    }
    #[doc = "Bits 14:23 - XTAL wait cycles in slow_clk_rtc"]
    #[inline(always)]
    pub fn xtl_buf_wait(&self) -> XTL_BUF_WAIT_R {
        XTL_BUF_WAIT_R::new(((self.bits >> 14) & 0x03ff) as u16)
    }
    #[doc = "Bits 24:31 - PLL wait cycles in slow_clk_rtc"]
    #[inline(always)]
    pub fn pll_buf_wait(&self) -> PLL_BUF_WAIT_R {
        PLL_BUF_WAIT_R::new(((self.bits >> 24) & 0xff) as u8)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("TIMER1")
            .field("cpu_stall_en", &self.cpu_stall_en())
            .field("cpu_stall_wait", &self.cpu_stall_wait())
            .field("ck8m_wait", &self.ck8m_wait())
            .field("xtl_buf_wait", &self.xtl_buf_wait())
            .field("pll_buf_wait", &self.pll_buf_wait())
            .finish()
    }
}
impl W {
    #[doc = "Bit 0 - CPU stall enable bit"]
    #[inline(always)]
    pub fn cpu_stall_en(&mut self) -> CPU_STALL_EN_W<'_, TIMER1_SPEC> {
        CPU_STALL_EN_W::new(self, 0)
    }
    #[doc = "Bits 1:5 - CPU stall wait cycles in fast_clk_rtc"]
    #[inline(always)]
    pub fn cpu_stall_wait(&mut self) -> CPU_STALL_WAIT_W<'_, TIMER1_SPEC> {
        CPU_STALL_WAIT_W::new(self, 1)
    }
    #[doc = "Bits 6:13 - CK8M wait cycles in slow_clk_rtc"]
    #[inline(always)]
    pub fn ck8m_wait(&mut self) -> CK8M_WAIT_W<'_, TIMER1_SPEC> {
        CK8M_WAIT_W::new(self, 6)
    }
    #[doc = "Bits 14:23 - XTAL wait cycles in slow_clk_rtc"]
    #[inline(always)]
    pub fn xtl_buf_wait(&mut self) -> XTL_BUF_WAIT_W<'_, TIMER1_SPEC> {
        XTL_BUF_WAIT_W::new(self, 14)
    }
    #[doc = "Bits 24:31 - PLL wait cycles in slow_clk_rtc"]
    #[inline(always)]
    pub fn pll_buf_wait(&mut self) -> PLL_BUF_WAIT_W<'_, TIMER1_SPEC> {
        PLL_BUF_WAIT_W::new(self, 24)
    }
}
#[doc = "rtc configure register\n\nYou can [`read`](crate::Reg::read) this register and get [`timer1::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`timer1::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct TIMER1_SPEC;
impl crate::RegisterSpec for TIMER1_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`timer1::R`](R) reader structure"]
impl crate::Readable for TIMER1_SPEC {}
#[doc = "`write(|w| ..)` method takes [`timer1::W`](W) writer structure"]
impl crate::Writable for TIMER1_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets TIMER1 to value 0x2814_0403"]
impl crate::Resettable for TIMER1_SPEC {
    const RESET_VALUE: u32 = 0x2814_0403;
}
