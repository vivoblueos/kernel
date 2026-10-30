#[doc = "Register `TSENS_CTRL` reader"]
pub type R = crate::R<TSENS_CTRL_SPEC>;
#[doc = "Register `TSENS_CTRL` writer"]
pub type W = crate::W<TSENS_CTRL_SPEC>;
#[doc = "Field `OUT` reader - temperature sensor data out"]
pub type OUT_R = crate::FieldReader;
#[doc = "Field `IN_INV` reader - invert temperature sensor data"]
pub type IN_INV_R = crate::BitReader;
#[doc = "Field `IN_INV` writer - invert temperature sensor data"]
pub type IN_INV_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `CLK_DIV` reader - temperature sensor clock divider"]
pub type CLK_DIV_R = crate::FieldReader;
#[doc = "Field `CLK_DIV` writer - temperature sensor clock divider"]
pub type CLK_DIV_W<'a, REG> = crate::FieldWriter<'a, REG, 8>;
#[doc = "Field `PU` reader - temperature sensor power up"]
pub type PU_R = crate::BitReader;
#[doc = "Field `PU` writer - temperature sensor power up"]
pub type PU_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bits 0:7 - temperature sensor data out"]
    #[inline(always)]
    pub fn out(&self) -> OUT_R {
        OUT_R::new((self.bits & 0xff) as u8)
    }
    #[doc = "Bit 13 - invert temperature sensor data"]
    #[inline(always)]
    pub fn in_inv(&self) -> IN_INV_R {
        IN_INV_R::new(((self.bits >> 13) & 1) != 0)
    }
    #[doc = "Bits 14:21 - temperature sensor clock divider"]
    #[inline(always)]
    pub fn clk_div(&self) -> CLK_DIV_R {
        CLK_DIV_R::new(((self.bits >> 14) & 0xff) as u8)
    }
    #[doc = "Bit 22 - temperature sensor power up"]
    #[inline(always)]
    pub fn pu(&self) -> PU_R {
        PU_R::new(((self.bits >> 22) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("TSENS_CTRL")
            .field("out", &self.out())
            .field("in_inv", &self.in_inv())
            .field("clk_div", &self.clk_div())
            .field("pu", &self.pu())
            .finish()
    }
}
impl W {
    #[doc = "Bit 13 - invert temperature sensor data"]
    #[inline(always)]
    pub fn in_inv(&mut self) -> IN_INV_W<'_, TSENS_CTRL_SPEC> {
        IN_INV_W::new(self, 13)
    }
    #[doc = "Bits 14:21 - temperature sensor clock divider"]
    #[inline(always)]
    pub fn clk_div(&mut self) -> CLK_DIV_W<'_, TSENS_CTRL_SPEC> {
        CLK_DIV_W::new(self, 14)
    }
    #[doc = "Bit 22 - temperature sensor power up"]
    #[inline(always)]
    pub fn pu(&mut self) -> PU_W<'_, TSENS_CTRL_SPEC> {
        PU_W::new(self, 22)
    }
}
#[doc = "digital tsens configure register\n\nYou can [`read`](crate::Reg::read) this register and get [`tsens_ctrl::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`tsens_ctrl::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct TSENS_CTRL_SPEC;
impl crate::RegisterSpec for TSENS_CTRL_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`tsens_ctrl::R`](R) reader structure"]
impl crate::Readable for TSENS_CTRL_SPEC {}
#[doc = "`write(|w| ..)` method takes [`tsens_ctrl::W`](W) writer structure"]
impl crate::Writable for TSENS_CTRL_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets TSENS_CTRL to value 0x0001_8000"]
impl crate::Resettable for TSENS_CTRL_SPEC {
    const RESET_VALUE: u32 = 0x0001_8000;
}
