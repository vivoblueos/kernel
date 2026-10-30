#[doc = "Register `CLK_EN` reader"]
pub type R = crate::R<CLK_EN_SPEC>;
#[doc = "Register `CLK_EN` writer"]
pub type W = crate::W<CLK_EN_SPEC>;
#[doc = "Field `LP_TOUCH_CK_EN` reader - need_des"]
pub type LP_TOUCH_CK_EN_R = crate::BitReader;
#[doc = "Field `LP_TOUCH_CK_EN` writer - need_des"]
pub type LP_TOUCH_CK_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `RNG_CK_EN` reader - need_des"]
pub type RNG_CK_EN_R = crate::BitReader;
#[doc = "Field `RNG_CK_EN` writer - need_des"]
pub type RNG_CK_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `OTP_DBG_CK_EN` reader - need_des"]
pub type OTP_DBG_CK_EN_R = crate::BitReader;
#[doc = "Field `OTP_DBG_CK_EN` writer - need_des"]
pub type OTP_DBG_CK_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `LP_UART_CK_EN` reader - need_des"]
pub type LP_UART_CK_EN_R = crate::BitReader;
#[doc = "Field `LP_UART_CK_EN` writer - need_des"]
pub type LP_UART_CK_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `LP_IO_CK_EN` reader - need_des"]
pub type LP_IO_CK_EN_R = crate::BitReader;
#[doc = "Field `LP_IO_CK_EN` writer - need_des"]
pub type LP_IO_CK_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `LP_EXT_I2C_CK_EN` reader - need_des"]
pub type LP_EXT_I2C_CK_EN_R = crate::BitReader;
#[doc = "Field `LP_EXT_I2C_CK_EN` writer - need_des"]
pub type LP_EXT_I2C_CK_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `LP_ANA_I2C_CK_EN` reader - need_des"]
pub type LP_ANA_I2C_CK_EN_R = crate::BitReader;
#[doc = "Field `LP_ANA_I2C_CK_EN` writer - need_des"]
pub type LP_ANA_I2C_CK_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `EFUSE_CK_EN` reader - need_des"]
pub type EFUSE_CK_EN_R = crate::BitReader;
#[doc = "Field `EFUSE_CK_EN` writer - need_des"]
pub type EFUSE_CK_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `LP_CPU_CK_EN` reader - need_des"]
pub type LP_CPU_CK_EN_R = crate::BitReader;
#[doc = "Field `LP_CPU_CK_EN` writer - need_des"]
pub type LP_CPU_CK_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 23 - need_des"]
    #[inline(always)]
    pub fn lp_touch_ck_en(&self) -> LP_TOUCH_CK_EN_R {
        LP_TOUCH_CK_EN_R::new(((self.bits >> 23) & 1) != 0)
    }
    #[doc = "Bit 24 - need_des"]
    #[inline(always)]
    pub fn rng_ck_en(&self) -> RNG_CK_EN_R {
        RNG_CK_EN_R::new(((self.bits >> 24) & 1) != 0)
    }
    #[doc = "Bit 25 - need_des"]
    #[inline(always)]
    pub fn otp_dbg_ck_en(&self) -> OTP_DBG_CK_EN_R {
        OTP_DBG_CK_EN_R::new(((self.bits >> 25) & 1) != 0)
    }
    #[doc = "Bit 26 - need_des"]
    #[inline(always)]
    pub fn lp_uart_ck_en(&self) -> LP_UART_CK_EN_R {
        LP_UART_CK_EN_R::new(((self.bits >> 26) & 1) != 0)
    }
    #[doc = "Bit 27 - need_des"]
    #[inline(always)]
    pub fn lp_io_ck_en(&self) -> LP_IO_CK_EN_R {
        LP_IO_CK_EN_R::new(((self.bits >> 27) & 1) != 0)
    }
    #[doc = "Bit 28 - need_des"]
    #[inline(always)]
    pub fn lp_ext_i2c_ck_en(&self) -> LP_EXT_I2C_CK_EN_R {
        LP_EXT_I2C_CK_EN_R::new(((self.bits >> 28) & 1) != 0)
    }
    #[doc = "Bit 29 - need_des"]
    #[inline(always)]
    pub fn lp_ana_i2c_ck_en(&self) -> LP_ANA_I2C_CK_EN_R {
        LP_ANA_I2C_CK_EN_R::new(((self.bits >> 29) & 1) != 0)
    }
    #[doc = "Bit 30 - need_des"]
    #[inline(always)]
    pub fn efuse_ck_en(&self) -> EFUSE_CK_EN_R {
        EFUSE_CK_EN_R::new(((self.bits >> 30) & 1) != 0)
    }
    #[doc = "Bit 31 - need_des"]
    #[inline(always)]
    pub fn lp_cpu_ck_en(&self) -> LP_CPU_CK_EN_R {
        LP_CPU_CK_EN_R::new(((self.bits >> 31) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("CLK_EN")
            .field("lp_touch_ck_en", &self.lp_touch_ck_en())
            .field("rng_ck_en", &self.rng_ck_en())
            .field("otp_dbg_ck_en", &self.otp_dbg_ck_en())
            .field("lp_uart_ck_en", &self.lp_uart_ck_en())
            .field("lp_io_ck_en", &self.lp_io_ck_en())
            .field("lp_ext_i2c_ck_en", &self.lp_ext_i2c_ck_en())
            .field("lp_ana_i2c_ck_en", &self.lp_ana_i2c_ck_en())
            .field("efuse_ck_en", &self.efuse_ck_en())
            .field("lp_cpu_ck_en", &self.lp_cpu_ck_en())
            .finish()
    }
}
impl W {
    #[doc = "Bit 23 - need_des"]
    #[inline(always)]
    pub fn lp_touch_ck_en(&mut self) -> LP_TOUCH_CK_EN_W<'_, CLK_EN_SPEC> {
        LP_TOUCH_CK_EN_W::new(self, 23)
    }
    #[doc = "Bit 24 - need_des"]
    #[inline(always)]
    pub fn rng_ck_en(&mut self) -> RNG_CK_EN_W<'_, CLK_EN_SPEC> {
        RNG_CK_EN_W::new(self, 24)
    }
    #[doc = "Bit 25 - need_des"]
    #[inline(always)]
    pub fn otp_dbg_ck_en(&mut self) -> OTP_DBG_CK_EN_W<'_, CLK_EN_SPEC> {
        OTP_DBG_CK_EN_W::new(self, 25)
    }
    #[doc = "Bit 26 - need_des"]
    #[inline(always)]
    pub fn lp_uart_ck_en(&mut self) -> LP_UART_CK_EN_W<'_, CLK_EN_SPEC> {
        LP_UART_CK_EN_W::new(self, 26)
    }
    #[doc = "Bit 27 - need_des"]
    #[inline(always)]
    pub fn lp_io_ck_en(&mut self) -> LP_IO_CK_EN_W<'_, CLK_EN_SPEC> {
        LP_IO_CK_EN_W::new(self, 27)
    }
    #[doc = "Bit 28 - need_des"]
    #[inline(always)]
    pub fn lp_ext_i2c_ck_en(&mut self) -> LP_EXT_I2C_CK_EN_W<'_, CLK_EN_SPEC> {
        LP_EXT_I2C_CK_EN_W::new(self, 28)
    }
    #[doc = "Bit 29 - need_des"]
    #[inline(always)]
    pub fn lp_ana_i2c_ck_en(&mut self) -> LP_ANA_I2C_CK_EN_W<'_, CLK_EN_SPEC> {
        LP_ANA_I2C_CK_EN_W::new(self, 29)
    }
    #[doc = "Bit 30 - need_des"]
    #[inline(always)]
    pub fn efuse_ck_en(&mut self) -> EFUSE_CK_EN_W<'_, CLK_EN_SPEC> {
        EFUSE_CK_EN_W::new(self, 30)
    }
    #[doc = "Bit 31 - need_des"]
    #[inline(always)]
    pub fn lp_cpu_ck_en(&mut self) -> LP_CPU_CK_EN_W<'_, CLK_EN_SPEC> {
        LP_CPU_CK_EN_W::new(self, 31)
    }
}
#[doc = "need_des\n\nYou can [`read`](crate::Reg::read) this register and get [`clk_en::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`clk_en::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct CLK_EN_SPEC;
impl crate::RegisterSpec for CLK_EN_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`clk_en::R`](R) reader structure"]
impl crate::Readable for CLK_EN_SPEC {}
#[doc = "`write(|w| ..)` method takes [`clk_en::W`](W) writer structure"]
impl crate::Writable for CLK_EN_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets CLK_EN to value 0x7f80_0000"]
impl crate::Resettable for CLK_EN_SPEC {
    const RESET_VALUE: u32 = 0x7f80_0000;
}
