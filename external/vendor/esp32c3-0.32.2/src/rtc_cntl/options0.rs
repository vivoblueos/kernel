#[doc = "Register `OPTIONS0` reader"]
pub type R = crate::R<OPTIONS0_SPEC>;
#[doc = "Register `OPTIONS0` writer"]
pub type W = crate::W<OPTIONS0_SPEC>;
#[doc = "Field `SW_STALL_APPCPU_C0` reader - {reg_sw_stall_appcpu_c1\\[5:0\\], reg_sw_stall_appcpu_c0\\[1:0\\]} == 0x86 will stall APP CPU"]
pub type SW_STALL_APPCPU_C0_R = crate::FieldReader;
#[doc = "Field `SW_STALL_APPCPU_C0` writer - {reg_sw_stall_appcpu_c1\\[5:0\\], reg_sw_stall_appcpu_c0\\[1:0\\]} == 0x86 will stall APP CPU"]
pub type SW_STALL_APPCPU_C0_W<'a, REG> = crate::FieldWriter<'a, REG, 2>;
#[doc = "Field `SW_STALL_PROCPU_C0` reader - {reg_sw_stall_procpu_c1\\[5:0\\], reg_sw_stall_procpu_c0\\[1:0\\]} == 0x86 will stall PRO CPU"]
pub type SW_STALL_PROCPU_C0_R = crate::FieldReader;
#[doc = "Field `SW_STALL_PROCPU_C0` writer - {reg_sw_stall_procpu_c1\\[5:0\\], reg_sw_stall_procpu_c0\\[1:0\\]} == 0x86 will stall PRO CPU"]
pub type SW_STALL_PROCPU_C0_W<'a, REG> = crate::FieldWriter<'a, REG, 2>;
#[doc = "Field `SW_APPCPU_RST` writer - APP CPU SW reset"]
pub type SW_APPCPU_RST_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SW_PROCPU_RST` writer - PRO CPU SW reset"]
pub type SW_PROCPU_RST_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `BB_I2C_FORCE_PD` reader - BB_I2C force power down"]
pub type BB_I2C_FORCE_PD_R = crate::BitReader;
#[doc = "Field `BB_I2C_FORCE_PD` writer - BB_I2C force power down"]
pub type BB_I2C_FORCE_PD_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `BB_I2C_FORCE_PU` reader - BB_I2C force power up"]
pub type BB_I2C_FORCE_PU_R = crate::BitReader;
#[doc = "Field `BB_I2C_FORCE_PU` writer - BB_I2C force power up"]
pub type BB_I2C_FORCE_PU_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `BBPLL_I2C_FORCE_PD` reader - BB_PLL _I2C force power down"]
pub type BBPLL_I2C_FORCE_PD_R = crate::BitReader;
#[doc = "Field `BBPLL_I2C_FORCE_PD` writer - BB_PLL _I2C force power down"]
pub type BBPLL_I2C_FORCE_PD_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `BBPLL_I2C_FORCE_PU` reader - BB_PLL_I2C force power up"]
pub type BBPLL_I2C_FORCE_PU_R = crate::BitReader;
#[doc = "Field `BBPLL_I2C_FORCE_PU` writer - BB_PLL_I2C force power up"]
pub type BBPLL_I2C_FORCE_PU_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `BBPLL_FORCE_PD` reader - BB_PLL force power down"]
pub type BBPLL_FORCE_PD_R = crate::BitReader;
#[doc = "Field `BBPLL_FORCE_PD` writer - BB_PLL force power down"]
pub type BBPLL_FORCE_PD_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `BBPLL_FORCE_PU` reader - BB_PLL force power up"]
pub type BBPLL_FORCE_PU_R = crate::BitReader;
#[doc = "Field `BBPLL_FORCE_PU` writer - BB_PLL force power up"]
pub type BBPLL_FORCE_PU_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `XTL_FORCE_PD` reader - crystall force power down"]
pub type XTL_FORCE_PD_R = crate::BitReader;
#[doc = "Field `XTL_FORCE_PD` writer - crystall force power down"]
pub type XTL_FORCE_PD_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `XTL_FORCE_PU` reader - crystall force power up"]
pub type XTL_FORCE_PU_R = crate::BitReader;
#[doc = "Field `XTL_FORCE_PU` writer - crystall force power up"]
pub type XTL_FORCE_PU_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `XTL_EN_WAIT` reader - wait bias_sleep and current source wakeup"]
pub type XTL_EN_WAIT_R = crate::FieldReader;
#[doc = "Field `XTL_EN_WAIT` writer - wait bias_sleep and current source wakeup"]
pub type XTL_EN_WAIT_W<'a, REG> = crate::FieldWriter<'a, REG, 4>;
#[doc = "Field `XTL_EXT_CTR_SEL` reader - analog configure"]
pub type XTL_EXT_CTR_SEL_R = crate::FieldReader;
#[doc = "Field `XTL_EXT_CTR_SEL` writer - analog configure"]
pub type XTL_EXT_CTR_SEL_W<'a, REG> = crate::FieldWriter<'a, REG, 3>;
#[doc = "Field `XTL_FORCE_ISO` reader - analog configure"]
pub type XTL_FORCE_ISO_R = crate::BitReader;
#[doc = "Field `XTL_FORCE_ISO` writer - analog configure"]
pub type XTL_FORCE_ISO_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `PLL_FORCE_ISO` reader - analog configure"]
pub type PLL_FORCE_ISO_R = crate::BitReader;
#[doc = "Field `PLL_FORCE_ISO` writer - analog configure"]
pub type PLL_FORCE_ISO_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ANALOG_FORCE_ISO` reader - analog configure"]
pub type ANALOG_FORCE_ISO_R = crate::BitReader;
#[doc = "Field `ANALOG_FORCE_ISO` writer - analog configure"]
pub type ANALOG_FORCE_ISO_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `XTL_FORCE_NOISO` reader - analog configure"]
pub type XTL_FORCE_NOISO_R = crate::BitReader;
#[doc = "Field `XTL_FORCE_NOISO` writer - analog configure"]
pub type XTL_FORCE_NOISO_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `PLL_FORCE_NOISO` reader - analog configure"]
pub type PLL_FORCE_NOISO_R = crate::BitReader;
#[doc = "Field `PLL_FORCE_NOISO` writer - analog configure"]
pub type PLL_FORCE_NOISO_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ANALOG_FORCE_NOISO` reader - analog configure"]
pub type ANALOG_FORCE_NOISO_R = crate::BitReader;
#[doc = "Field `ANALOG_FORCE_NOISO` writer - analog configure"]
pub type ANALOG_FORCE_NOISO_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `DG_WRAP_FORCE_RST` reader - digital wrap force reset in deep sleep"]
pub type DG_WRAP_FORCE_RST_R = crate::BitReader;
#[doc = "Field `DG_WRAP_FORCE_RST` writer - digital wrap force reset in deep sleep"]
pub type DG_WRAP_FORCE_RST_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `DG_WRAP_FORCE_NORST` reader - digital core force no reset in deep sleep"]
pub type DG_WRAP_FORCE_NORST_R = crate::BitReader;
#[doc = "Field `DG_WRAP_FORCE_NORST` writer - digital core force no reset in deep sleep"]
pub type DG_WRAP_FORCE_NORST_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SW_SYS_RST` writer - SW system reset"]
pub type SW_SYS_RST_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bits 0:1 - {reg_sw_stall_appcpu_c1\\[5:0\\], reg_sw_stall_appcpu_c0\\[1:0\\]} == 0x86 will stall APP CPU"]
    #[inline(always)]
    pub fn sw_stall_appcpu_c0(&self) -> SW_STALL_APPCPU_C0_R {
        SW_STALL_APPCPU_C0_R::new((self.bits & 3) as u8)
    }
    #[doc = "Bits 2:3 - {reg_sw_stall_procpu_c1\\[5:0\\], reg_sw_stall_procpu_c0\\[1:0\\]} == 0x86 will stall PRO CPU"]
    #[inline(always)]
    pub fn sw_stall_procpu_c0(&self) -> SW_STALL_PROCPU_C0_R {
        SW_STALL_PROCPU_C0_R::new(((self.bits >> 2) & 3) as u8)
    }
    #[doc = "Bit 6 - BB_I2C force power down"]
    #[inline(always)]
    pub fn bb_i2c_force_pd(&self) -> BB_I2C_FORCE_PD_R {
        BB_I2C_FORCE_PD_R::new(((self.bits >> 6) & 1) != 0)
    }
    #[doc = "Bit 7 - BB_I2C force power up"]
    #[inline(always)]
    pub fn bb_i2c_force_pu(&self) -> BB_I2C_FORCE_PU_R {
        BB_I2C_FORCE_PU_R::new(((self.bits >> 7) & 1) != 0)
    }
    #[doc = "Bit 8 - BB_PLL _I2C force power down"]
    #[inline(always)]
    pub fn bbpll_i2c_force_pd(&self) -> BBPLL_I2C_FORCE_PD_R {
        BBPLL_I2C_FORCE_PD_R::new(((self.bits >> 8) & 1) != 0)
    }
    #[doc = "Bit 9 - BB_PLL_I2C force power up"]
    #[inline(always)]
    pub fn bbpll_i2c_force_pu(&self) -> BBPLL_I2C_FORCE_PU_R {
        BBPLL_I2C_FORCE_PU_R::new(((self.bits >> 9) & 1) != 0)
    }
    #[doc = "Bit 10 - BB_PLL force power down"]
    #[inline(always)]
    pub fn bbpll_force_pd(&self) -> BBPLL_FORCE_PD_R {
        BBPLL_FORCE_PD_R::new(((self.bits >> 10) & 1) != 0)
    }
    #[doc = "Bit 11 - BB_PLL force power up"]
    #[inline(always)]
    pub fn bbpll_force_pu(&self) -> BBPLL_FORCE_PU_R {
        BBPLL_FORCE_PU_R::new(((self.bits >> 11) & 1) != 0)
    }
    #[doc = "Bit 12 - crystall force power down"]
    #[inline(always)]
    pub fn xtl_force_pd(&self) -> XTL_FORCE_PD_R {
        XTL_FORCE_PD_R::new(((self.bits >> 12) & 1) != 0)
    }
    #[doc = "Bit 13 - crystall force power up"]
    #[inline(always)]
    pub fn xtl_force_pu(&self) -> XTL_FORCE_PU_R {
        XTL_FORCE_PU_R::new(((self.bits >> 13) & 1) != 0)
    }
    #[doc = "Bits 14:17 - wait bias_sleep and current source wakeup"]
    #[inline(always)]
    pub fn xtl_en_wait(&self) -> XTL_EN_WAIT_R {
        XTL_EN_WAIT_R::new(((self.bits >> 14) & 0x0f) as u8)
    }
    #[doc = "Bits 20:22 - analog configure"]
    #[inline(always)]
    pub fn xtl_ext_ctr_sel(&self) -> XTL_EXT_CTR_SEL_R {
        XTL_EXT_CTR_SEL_R::new(((self.bits >> 20) & 7) as u8)
    }
    #[doc = "Bit 23 - analog configure"]
    #[inline(always)]
    pub fn xtl_force_iso(&self) -> XTL_FORCE_ISO_R {
        XTL_FORCE_ISO_R::new(((self.bits >> 23) & 1) != 0)
    }
    #[doc = "Bit 24 - analog configure"]
    #[inline(always)]
    pub fn pll_force_iso(&self) -> PLL_FORCE_ISO_R {
        PLL_FORCE_ISO_R::new(((self.bits >> 24) & 1) != 0)
    }
    #[doc = "Bit 25 - analog configure"]
    #[inline(always)]
    pub fn analog_force_iso(&self) -> ANALOG_FORCE_ISO_R {
        ANALOG_FORCE_ISO_R::new(((self.bits >> 25) & 1) != 0)
    }
    #[doc = "Bit 26 - analog configure"]
    #[inline(always)]
    pub fn xtl_force_noiso(&self) -> XTL_FORCE_NOISO_R {
        XTL_FORCE_NOISO_R::new(((self.bits >> 26) & 1) != 0)
    }
    #[doc = "Bit 27 - analog configure"]
    #[inline(always)]
    pub fn pll_force_noiso(&self) -> PLL_FORCE_NOISO_R {
        PLL_FORCE_NOISO_R::new(((self.bits >> 27) & 1) != 0)
    }
    #[doc = "Bit 28 - analog configure"]
    #[inline(always)]
    pub fn analog_force_noiso(&self) -> ANALOG_FORCE_NOISO_R {
        ANALOG_FORCE_NOISO_R::new(((self.bits >> 28) & 1) != 0)
    }
    #[doc = "Bit 29 - digital wrap force reset in deep sleep"]
    #[inline(always)]
    pub fn dg_wrap_force_rst(&self) -> DG_WRAP_FORCE_RST_R {
        DG_WRAP_FORCE_RST_R::new(((self.bits >> 29) & 1) != 0)
    }
    #[doc = "Bit 30 - digital core force no reset in deep sleep"]
    #[inline(always)]
    pub fn dg_wrap_force_norst(&self) -> DG_WRAP_FORCE_NORST_R {
        DG_WRAP_FORCE_NORST_R::new(((self.bits >> 30) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("OPTIONS0")
            .field("sw_stall_appcpu_c0", &self.sw_stall_appcpu_c0())
            .field("sw_stall_procpu_c0", &self.sw_stall_procpu_c0())
            .field("bb_i2c_force_pd", &self.bb_i2c_force_pd())
            .field("bb_i2c_force_pu", &self.bb_i2c_force_pu())
            .field("bbpll_i2c_force_pd", &self.bbpll_i2c_force_pd())
            .field("bbpll_i2c_force_pu", &self.bbpll_i2c_force_pu())
            .field("bbpll_force_pd", &self.bbpll_force_pd())
            .field("bbpll_force_pu", &self.bbpll_force_pu())
            .field("xtl_force_pd", &self.xtl_force_pd())
            .field("xtl_force_pu", &self.xtl_force_pu())
            .field("xtl_en_wait", &self.xtl_en_wait())
            .field("xtl_ext_ctr_sel", &self.xtl_ext_ctr_sel())
            .field("xtl_force_iso", &self.xtl_force_iso())
            .field("pll_force_iso", &self.pll_force_iso())
            .field("analog_force_iso", &self.analog_force_iso())
            .field("xtl_force_noiso", &self.xtl_force_noiso())
            .field("pll_force_noiso", &self.pll_force_noiso())
            .field("analog_force_noiso", &self.analog_force_noiso())
            .field("dg_wrap_force_rst", &self.dg_wrap_force_rst())
            .field("dg_wrap_force_norst", &self.dg_wrap_force_norst())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:1 - {reg_sw_stall_appcpu_c1\\[5:0\\], reg_sw_stall_appcpu_c0\\[1:0\\]} == 0x86 will stall APP CPU"]
    #[inline(always)]
    pub fn sw_stall_appcpu_c0(&mut self) -> SW_STALL_APPCPU_C0_W<'_, OPTIONS0_SPEC> {
        SW_STALL_APPCPU_C0_W::new(self, 0)
    }
    #[doc = "Bits 2:3 - {reg_sw_stall_procpu_c1\\[5:0\\], reg_sw_stall_procpu_c0\\[1:0\\]} == 0x86 will stall PRO CPU"]
    #[inline(always)]
    pub fn sw_stall_procpu_c0(&mut self) -> SW_STALL_PROCPU_C0_W<'_, OPTIONS0_SPEC> {
        SW_STALL_PROCPU_C0_W::new(self, 2)
    }
    #[doc = "Bit 4 - APP CPU SW reset"]
    #[inline(always)]
    pub fn sw_appcpu_rst(&mut self) -> SW_APPCPU_RST_W<'_, OPTIONS0_SPEC> {
        SW_APPCPU_RST_W::new(self, 4)
    }
    #[doc = "Bit 5 - PRO CPU SW reset"]
    #[inline(always)]
    pub fn sw_procpu_rst(&mut self) -> SW_PROCPU_RST_W<'_, OPTIONS0_SPEC> {
        SW_PROCPU_RST_W::new(self, 5)
    }
    #[doc = "Bit 6 - BB_I2C force power down"]
    #[inline(always)]
    pub fn bb_i2c_force_pd(&mut self) -> BB_I2C_FORCE_PD_W<'_, OPTIONS0_SPEC> {
        BB_I2C_FORCE_PD_W::new(self, 6)
    }
    #[doc = "Bit 7 - BB_I2C force power up"]
    #[inline(always)]
    pub fn bb_i2c_force_pu(&mut self) -> BB_I2C_FORCE_PU_W<'_, OPTIONS0_SPEC> {
        BB_I2C_FORCE_PU_W::new(self, 7)
    }
    #[doc = "Bit 8 - BB_PLL _I2C force power down"]
    #[inline(always)]
    pub fn bbpll_i2c_force_pd(&mut self) -> BBPLL_I2C_FORCE_PD_W<'_, OPTIONS0_SPEC> {
        BBPLL_I2C_FORCE_PD_W::new(self, 8)
    }
    #[doc = "Bit 9 - BB_PLL_I2C force power up"]
    #[inline(always)]
    pub fn bbpll_i2c_force_pu(&mut self) -> BBPLL_I2C_FORCE_PU_W<'_, OPTIONS0_SPEC> {
        BBPLL_I2C_FORCE_PU_W::new(self, 9)
    }
    #[doc = "Bit 10 - BB_PLL force power down"]
    #[inline(always)]
    pub fn bbpll_force_pd(&mut self) -> BBPLL_FORCE_PD_W<'_, OPTIONS0_SPEC> {
        BBPLL_FORCE_PD_W::new(self, 10)
    }
    #[doc = "Bit 11 - BB_PLL force power up"]
    #[inline(always)]
    pub fn bbpll_force_pu(&mut self) -> BBPLL_FORCE_PU_W<'_, OPTIONS0_SPEC> {
        BBPLL_FORCE_PU_W::new(self, 11)
    }
    #[doc = "Bit 12 - crystall force power down"]
    #[inline(always)]
    pub fn xtl_force_pd(&mut self) -> XTL_FORCE_PD_W<'_, OPTIONS0_SPEC> {
        XTL_FORCE_PD_W::new(self, 12)
    }
    #[doc = "Bit 13 - crystall force power up"]
    #[inline(always)]
    pub fn xtl_force_pu(&mut self) -> XTL_FORCE_PU_W<'_, OPTIONS0_SPEC> {
        XTL_FORCE_PU_W::new(self, 13)
    }
    #[doc = "Bits 14:17 - wait bias_sleep and current source wakeup"]
    #[inline(always)]
    pub fn xtl_en_wait(&mut self) -> XTL_EN_WAIT_W<'_, OPTIONS0_SPEC> {
        XTL_EN_WAIT_W::new(self, 14)
    }
    #[doc = "Bits 20:22 - analog configure"]
    #[inline(always)]
    pub fn xtl_ext_ctr_sel(&mut self) -> XTL_EXT_CTR_SEL_W<'_, OPTIONS0_SPEC> {
        XTL_EXT_CTR_SEL_W::new(self, 20)
    }
    #[doc = "Bit 23 - analog configure"]
    #[inline(always)]
    pub fn xtl_force_iso(&mut self) -> XTL_FORCE_ISO_W<'_, OPTIONS0_SPEC> {
        XTL_FORCE_ISO_W::new(self, 23)
    }
    #[doc = "Bit 24 - analog configure"]
    #[inline(always)]
    pub fn pll_force_iso(&mut self) -> PLL_FORCE_ISO_W<'_, OPTIONS0_SPEC> {
        PLL_FORCE_ISO_W::new(self, 24)
    }
    #[doc = "Bit 25 - analog configure"]
    #[inline(always)]
    pub fn analog_force_iso(&mut self) -> ANALOG_FORCE_ISO_W<'_, OPTIONS0_SPEC> {
        ANALOG_FORCE_ISO_W::new(self, 25)
    }
    #[doc = "Bit 26 - analog configure"]
    #[inline(always)]
    pub fn xtl_force_noiso(&mut self) -> XTL_FORCE_NOISO_W<'_, OPTIONS0_SPEC> {
        XTL_FORCE_NOISO_W::new(self, 26)
    }
    #[doc = "Bit 27 - analog configure"]
    #[inline(always)]
    pub fn pll_force_noiso(&mut self) -> PLL_FORCE_NOISO_W<'_, OPTIONS0_SPEC> {
        PLL_FORCE_NOISO_W::new(self, 27)
    }
    #[doc = "Bit 28 - analog configure"]
    #[inline(always)]
    pub fn analog_force_noiso(&mut self) -> ANALOG_FORCE_NOISO_W<'_, OPTIONS0_SPEC> {
        ANALOG_FORCE_NOISO_W::new(self, 28)
    }
    #[doc = "Bit 29 - digital wrap force reset in deep sleep"]
    #[inline(always)]
    pub fn dg_wrap_force_rst(&mut self) -> DG_WRAP_FORCE_RST_W<'_, OPTIONS0_SPEC> {
        DG_WRAP_FORCE_RST_W::new(self, 29)
    }
    #[doc = "Bit 30 - digital core force no reset in deep sleep"]
    #[inline(always)]
    pub fn dg_wrap_force_norst(&mut self) -> DG_WRAP_FORCE_NORST_W<'_, OPTIONS0_SPEC> {
        DG_WRAP_FORCE_NORST_W::new(self, 30)
    }
    #[doc = "Bit 31 - SW system reset"]
    #[inline(always)]
    pub fn sw_sys_rst(&mut self) -> SW_SYS_RST_W<'_, OPTIONS0_SPEC> {
        SW_SYS_RST_W::new(self, 31)
    }
}
#[doc = "rtc configure register\n\nYou can [`read`](crate::Reg::read) this register and get [`options0::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`options0::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct OPTIONS0_SPEC;
impl crate::RegisterSpec for OPTIONS0_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`options0::R`](R) reader structure"]
impl crate::Readable for OPTIONS0_SPEC {}
#[doc = "`write(|w| ..)` method takes [`options0::W`](W) writer structure"]
impl crate::Writable for OPTIONS0_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets OPTIONS0 to value 0x1c00_a000"]
impl crate::Resettable for OPTIONS0_SPEC {
    const RESET_VALUE: u32 = 0x1c00_a000;
}
