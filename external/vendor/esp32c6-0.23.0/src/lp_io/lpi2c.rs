#[doc = "Register `LPI2C` reader"]
pub type R = crate::R<LPI2C_SPEC>;
#[doc = "Register `LPI2C` writer"]
pub type W = crate::W<LPI2C_SPEC>;
#[doc = "Field `LP_I2C_SDA_IE` reader - need des"]
pub type LP_I2C_SDA_IE_R = crate::BitReader;
#[doc = "Field `LP_I2C_SDA_IE` writer - need des"]
pub type LP_I2C_SDA_IE_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `LP_I2C_SCL_IE` reader - need des"]
pub type LP_I2C_SCL_IE_R = crate::BitReader;
#[doc = "Field `LP_I2C_SCL_IE` writer - need des"]
pub type LP_I2C_SCL_IE_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 30 - need des"]
    #[inline(always)]
    pub fn lp_i2c_sda_ie(&self) -> LP_I2C_SDA_IE_R {
        LP_I2C_SDA_IE_R::new(((self.bits >> 30) & 1) != 0)
    }
    #[doc = "Bit 31 - need des"]
    #[inline(always)]
    pub fn lp_i2c_scl_ie(&self) -> LP_I2C_SCL_IE_R {
        LP_I2C_SCL_IE_R::new(((self.bits >> 31) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("LPI2C")
            .field("lp_i2c_sda_ie", &self.lp_i2c_sda_ie())
            .field("lp_i2c_scl_ie", &self.lp_i2c_scl_ie())
            .finish()
    }
}
impl W {
    #[doc = "Bit 30 - need des"]
    #[inline(always)]
    pub fn lp_i2c_sda_ie(&mut self) -> LP_I2C_SDA_IE_W<'_, LPI2C_SPEC> {
        LP_I2C_SDA_IE_W::new(self, 30)
    }
    #[doc = "Bit 31 - need des"]
    #[inline(always)]
    pub fn lp_i2c_scl_ie(&mut self) -> LP_I2C_SCL_IE_W<'_, LPI2C_SPEC> {
        LP_I2C_SCL_IE_W::new(self, 31)
    }
}
#[doc = "need des\n\nYou can [`read`](crate::Reg::read) this register and get [`lpi2c::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`lpi2c::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct LPI2C_SPEC;
impl crate::RegisterSpec for LPI2C_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`lpi2c::R`](R) reader structure"]
impl crate::Readable for LPI2C_SPEC {}
#[doc = "`write(|w| ..)` method takes [`lpi2c::W`](W) writer structure"]
impl crate::Writable for LPI2C_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets LPI2C to value 0xc000_0000"]
impl crate::Resettable for LPI2C_SPEC {
    const RESET_VALUE: u32 = 0xc000_0000;
}
