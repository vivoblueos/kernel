#[doc = "Register `TSENS_CTRL2` reader"]
pub type R = crate::R<TSENS_CTRL2_SPEC>;
#[doc = "Register `TSENS_CTRL2` writer"]
pub type W = crate::W<TSENS_CTRL2_SPEC>;
#[doc = "Field `XPD_WAIT` reader - the time that power up tsens need wait"]
pub type XPD_WAIT_R = crate::FieldReader<u16>;
#[doc = "Field `XPD_WAIT` writer - the time that power up tsens need wait"]
pub type XPD_WAIT_W<'a, REG> = crate::FieldWriter<'a, REG, 12, u16>;
#[doc = "Field `XPD_FORCE` reader - force power up tsens"]
pub type XPD_FORCE_R = crate::FieldReader;
#[doc = "Field `XPD_FORCE` writer - force power up tsens"]
pub type XPD_FORCE_W<'a, REG> = crate::FieldWriter<'a, REG, 2>;
#[doc = "Field `CLK_INV` reader - inv tsens clk"]
pub type CLK_INV_R = crate::BitReader;
#[doc = "Field `CLK_INV` writer - inv tsens clk"]
pub type CLK_INV_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `CLK_SEL` reader - tsens clk select"]
pub type CLK_SEL_R = crate::BitReader;
#[doc = "Field `CLK_SEL` writer - tsens clk select"]
pub type CLK_SEL_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bits 0:11 - the time that power up tsens need wait"]
    #[inline(always)]
    pub fn xpd_wait(&self) -> XPD_WAIT_R {
        XPD_WAIT_R::new((self.bits & 0x0fff) as u16)
    }
    #[doc = "Bits 12:13 - force power up tsens"]
    #[inline(always)]
    pub fn xpd_force(&self) -> XPD_FORCE_R {
        XPD_FORCE_R::new(((self.bits >> 12) & 3) as u8)
    }
    #[doc = "Bit 14 - inv tsens clk"]
    #[inline(always)]
    pub fn clk_inv(&self) -> CLK_INV_R {
        CLK_INV_R::new(((self.bits >> 14) & 1) != 0)
    }
    #[doc = "Bit 15 - tsens clk select"]
    #[inline(always)]
    pub fn clk_sel(&self) -> CLK_SEL_R {
        CLK_SEL_R::new(((self.bits >> 15) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("TSENS_CTRL2")
            .field("xpd_wait", &self.xpd_wait())
            .field("xpd_force", &self.xpd_force())
            .field("clk_inv", &self.clk_inv())
            .field("clk_sel", &self.clk_sel())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:11 - the time that power up tsens need wait"]
    #[inline(always)]
    pub fn xpd_wait(&mut self) -> XPD_WAIT_W<'_, TSENS_CTRL2_SPEC> {
        XPD_WAIT_W::new(self, 0)
    }
    #[doc = "Bits 12:13 - force power up tsens"]
    #[inline(always)]
    pub fn xpd_force(&mut self) -> XPD_FORCE_W<'_, TSENS_CTRL2_SPEC> {
        XPD_FORCE_W::new(self, 12)
    }
    #[doc = "Bit 14 - inv tsens clk"]
    #[inline(always)]
    pub fn clk_inv(&mut self) -> CLK_INV_W<'_, TSENS_CTRL2_SPEC> {
        CLK_INV_W::new(self, 14)
    }
    #[doc = "Bit 15 - tsens clk select"]
    #[inline(always)]
    pub fn clk_sel(&mut self) -> CLK_SEL_W<'_, TSENS_CTRL2_SPEC> {
        CLK_SEL_W::new(self, 15)
    }
}
#[doc = "digital tsens configure register\n\nYou can [`read`](crate::Reg::read) this register and get [`tsens_ctrl2::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`tsens_ctrl2::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct TSENS_CTRL2_SPEC;
impl crate::RegisterSpec for TSENS_CTRL2_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`tsens_ctrl2::R`](R) reader structure"]
impl crate::Readable for TSENS_CTRL2_SPEC {}
#[doc = "`write(|w| ..)` method takes [`tsens_ctrl2::W`](W) writer structure"]
impl crate::Writable for TSENS_CTRL2_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets TSENS_CTRL2 to value 0x4002"]
impl crate::Resettable for TSENS_CTRL2_SPEC {
    const RESET_VALUE: u32 = 0x4002;
}
