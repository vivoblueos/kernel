#[doc = "Register `RETENTION_CTRL` reader"]
pub type R = crate::R<RETENTION_CTRL_SPEC>;
#[doc = "Register `RETENTION_CTRL` writer"]
pub type W = crate::W<RETENTION_CTRL_SPEC>;
#[doc = "Field `RETENTION_CLK_SEL` reader - Retention clk sel"]
pub type RETENTION_CLK_SEL_R = crate::BitReader;
#[doc = "Field `RETENTION_CLK_SEL` writer - Retention clk sel"]
pub type RETENTION_CLK_SEL_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `RETENTION_DONE_WAIT` reader - Retention done wait time"]
pub type RETENTION_DONE_WAIT_R = crate::FieldReader;
#[doc = "Field `RETENTION_DONE_WAIT` writer - Retention done wait time"]
pub type RETENTION_DONE_WAIT_W<'a, REG> = crate::FieldWriter<'a, REG, 3>;
#[doc = "Field `RETENTION_CLKOFF_WAIT` reader - Retention clkoff wait time"]
pub type RETENTION_CLKOFF_WAIT_R = crate::FieldReader;
#[doc = "Field `RETENTION_CLKOFF_WAIT` writer - Retention clkoff wait time"]
pub type RETENTION_CLKOFF_WAIT_W<'a, REG> = crate::FieldWriter<'a, REG, 4>;
#[doc = "Field `RETENTION_EN` reader - enable cpu retention when light sleep"]
pub type RETENTION_EN_R = crate::BitReader;
#[doc = "Field `RETENTION_EN` writer - enable cpu retention when light sleep"]
pub type RETENTION_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `RETENTION_WAIT` reader - wait cycles for rention operation"]
pub type RETENTION_WAIT_R = crate::FieldReader;
#[doc = "Field `RETENTION_WAIT` writer - wait cycles for rention operation"]
pub type RETENTION_WAIT_W<'a, REG> = crate::FieldWriter<'a, REG, 5>;
impl R {
    #[doc = "Bit 18 - Retention clk sel"]
    #[inline(always)]
    pub fn retention_clk_sel(&self) -> RETENTION_CLK_SEL_R {
        RETENTION_CLK_SEL_R::new(((self.bits >> 18) & 1) != 0)
    }
    #[doc = "Bits 19:21 - Retention done wait time"]
    #[inline(always)]
    pub fn retention_done_wait(&self) -> RETENTION_DONE_WAIT_R {
        RETENTION_DONE_WAIT_R::new(((self.bits >> 19) & 7) as u8)
    }
    #[doc = "Bits 22:25 - Retention clkoff wait time"]
    #[inline(always)]
    pub fn retention_clkoff_wait(&self) -> RETENTION_CLKOFF_WAIT_R {
        RETENTION_CLKOFF_WAIT_R::new(((self.bits >> 22) & 0x0f) as u8)
    }
    #[doc = "Bit 26 - enable cpu retention when light sleep"]
    #[inline(always)]
    pub fn retention_en(&self) -> RETENTION_EN_R {
        RETENTION_EN_R::new(((self.bits >> 26) & 1) != 0)
    }
    #[doc = "Bits 27:31 - wait cycles for rention operation"]
    #[inline(always)]
    pub fn retention_wait(&self) -> RETENTION_WAIT_R {
        RETENTION_WAIT_R::new(((self.bits >> 27) & 0x1f) as u8)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("RETENTION_CTRL")
            .field("retention_clk_sel", &self.retention_clk_sel())
            .field("retention_done_wait", &self.retention_done_wait())
            .field("retention_clkoff_wait", &self.retention_clkoff_wait())
            .field("retention_en", &self.retention_en())
            .field("retention_wait", &self.retention_wait())
            .finish()
    }
}
impl W {
    #[doc = "Bit 18 - Retention clk sel"]
    #[inline(always)]
    pub fn retention_clk_sel(&mut self) -> RETENTION_CLK_SEL_W<'_, RETENTION_CTRL_SPEC> {
        RETENTION_CLK_SEL_W::new(self, 18)
    }
    #[doc = "Bits 19:21 - Retention done wait time"]
    #[inline(always)]
    pub fn retention_done_wait(&mut self) -> RETENTION_DONE_WAIT_W<'_, RETENTION_CTRL_SPEC> {
        RETENTION_DONE_WAIT_W::new(self, 19)
    }
    #[doc = "Bits 22:25 - Retention clkoff wait time"]
    #[inline(always)]
    pub fn retention_clkoff_wait(&mut self) -> RETENTION_CLKOFF_WAIT_W<'_, RETENTION_CTRL_SPEC> {
        RETENTION_CLKOFF_WAIT_W::new(self, 22)
    }
    #[doc = "Bit 26 - enable cpu retention when light sleep"]
    #[inline(always)]
    pub fn retention_en(&mut self) -> RETENTION_EN_W<'_, RETENTION_CTRL_SPEC> {
        RETENTION_EN_W::new(self, 26)
    }
    #[doc = "Bits 27:31 - wait cycles for rention operation"]
    #[inline(always)]
    pub fn retention_wait(&mut self) -> RETENTION_WAIT_W<'_, RETENTION_CTRL_SPEC> {
        RETENTION_WAIT_W::new(self, 27)
    }
}
#[doc = "rtc configure register\n\nYou can [`read`](crate::Reg::read) this register and get [`retention_ctrl::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`retention_ctrl::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct RETENTION_CTRL_SPEC;
impl crate::RegisterSpec for RETENTION_CTRL_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`retention_ctrl::R`](R) reader structure"]
impl crate::Readable for RETENTION_CTRL_SPEC {}
#[doc = "`write(|w| ..)` method takes [`retention_ctrl::W`](W) writer structure"]
impl crate::Writable for RETENTION_CTRL_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets RETENTION_CTRL to value 0xa0d0_0000"]
impl crate::Resettable for RETENTION_CTRL_SPEC {
    const RESET_VALUE: u32 = 0xa0d0_0000;
}
