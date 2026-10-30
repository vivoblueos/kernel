#[doc = "Register `I2C_SCLK_CONF` reader"]
pub type R = crate::R<I2C_SCLK_CONF_SPEC>;
#[doc = "Register `I2C_SCLK_CONF` writer"]
pub type W = crate::W<I2C_SCLK_CONF_SPEC>;
#[doc = "Field `I2C_SCLK_DIV_A` reader - The denominator of the frequency divider factor of the i2c function clock."]
pub type I2C_SCLK_DIV_A_R = crate::FieldReader;
#[doc = "Field `I2C_SCLK_DIV_A` writer - The denominator of the frequency divider factor of the i2c function clock."]
pub type I2C_SCLK_DIV_A_W<'a, REG> = crate::FieldWriter<'a, REG, 6>;
#[doc = "Field `I2C_SCLK_DIV_B` reader - The numerator of the frequency divider factor of the i2c function clock."]
pub type I2C_SCLK_DIV_B_R = crate::FieldReader;
#[doc = "Field `I2C_SCLK_DIV_B` writer - The numerator of the frequency divider factor of the i2c function clock."]
pub type I2C_SCLK_DIV_B_W<'a, REG> = crate::FieldWriter<'a, REG, 6>;
#[doc = "Field `I2C_SCLK_DIV_NUM` reader - The integral part of the frequency divider factor of the i2c function clock."]
pub type I2C_SCLK_DIV_NUM_R = crate::FieldReader;
#[doc = "Field `I2C_SCLK_DIV_NUM` writer - The integral part of the frequency divider factor of the i2c function clock."]
pub type I2C_SCLK_DIV_NUM_W<'a, REG> = crate::FieldWriter<'a, REG, 8>;
#[doc = "Field `I2C_SCLK_SEL` reader - set this field to select clock-source. 0(default): XTAL, 1: FOSC."]
pub type I2C_SCLK_SEL_R = crate::BitReader;
#[doc = "Field `I2C_SCLK_SEL` writer - set this field to select clock-source. 0(default): XTAL, 1: FOSC."]
pub type I2C_SCLK_SEL_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `I2C_SCLK_EN` reader - Set 1 to enable i2c function clock"]
pub type I2C_SCLK_EN_R = crate::BitReader;
#[doc = "Field `I2C_SCLK_EN` writer - Set 1 to enable i2c function clock"]
pub type I2C_SCLK_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bits 0:5 - The denominator of the frequency divider factor of the i2c function clock."]
    #[inline(always)]
    pub fn i2c_sclk_div_a(&self) -> I2C_SCLK_DIV_A_R {
        I2C_SCLK_DIV_A_R::new((self.bits & 0x3f) as u8)
    }
    #[doc = "Bits 6:11 - The numerator of the frequency divider factor of the i2c function clock."]
    #[inline(always)]
    pub fn i2c_sclk_div_b(&self) -> I2C_SCLK_DIV_B_R {
        I2C_SCLK_DIV_B_R::new(((self.bits >> 6) & 0x3f) as u8)
    }
    #[doc = "Bits 12:19 - The integral part of the frequency divider factor of the i2c function clock."]
    #[inline(always)]
    pub fn i2c_sclk_div_num(&self) -> I2C_SCLK_DIV_NUM_R {
        I2C_SCLK_DIV_NUM_R::new(((self.bits >> 12) & 0xff) as u8)
    }
    #[doc = "Bit 20 - set this field to select clock-source. 0(default): XTAL, 1: FOSC."]
    #[inline(always)]
    pub fn i2c_sclk_sel(&self) -> I2C_SCLK_SEL_R {
        I2C_SCLK_SEL_R::new(((self.bits >> 20) & 1) != 0)
    }
    #[doc = "Bit 22 - Set 1 to enable i2c function clock"]
    #[inline(always)]
    pub fn i2c_sclk_en(&self) -> I2C_SCLK_EN_R {
        I2C_SCLK_EN_R::new(((self.bits >> 22) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("I2C_SCLK_CONF")
            .field("i2c_sclk_div_a", &self.i2c_sclk_div_a())
            .field("i2c_sclk_div_b", &self.i2c_sclk_div_b())
            .field("i2c_sclk_div_num", &self.i2c_sclk_div_num())
            .field("i2c_sclk_sel", &self.i2c_sclk_sel())
            .field("i2c_sclk_en", &self.i2c_sclk_en())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:5 - The denominator of the frequency divider factor of the i2c function clock."]
    #[inline(always)]
    pub fn i2c_sclk_div_a(&mut self) -> I2C_SCLK_DIV_A_W<'_, I2C_SCLK_CONF_SPEC> {
        I2C_SCLK_DIV_A_W::new(self, 0)
    }
    #[doc = "Bits 6:11 - The numerator of the frequency divider factor of the i2c function clock."]
    #[inline(always)]
    pub fn i2c_sclk_div_b(&mut self) -> I2C_SCLK_DIV_B_W<'_, I2C_SCLK_CONF_SPEC> {
        I2C_SCLK_DIV_B_W::new(self, 6)
    }
    #[doc = "Bits 12:19 - The integral part of the frequency divider factor of the i2c function clock."]
    #[inline(always)]
    pub fn i2c_sclk_div_num(&mut self) -> I2C_SCLK_DIV_NUM_W<'_, I2C_SCLK_CONF_SPEC> {
        I2C_SCLK_DIV_NUM_W::new(self, 12)
    }
    #[doc = "Bit 20 - set this field to select clock-source. 0(default): XTAL, 1: FOSC."]
    #[inline(always)]
    pub fn i2c_sclk_sel(&mut self) -> I2C_SCLK_SEL_W<'_, I2C_SCLK_CONF_SPEC> {
        I2C_SCLK_SEL_W::new(self, 20)
    }
    #[doc = "Bit 22 - Set 1 to enable i2c function clock"]
    #[inline(always)]
    pub fn i2c_sclk_en(&mut self) -> I2C_SCLK_EN_W<'_, I2C_SCLK_CONF_SPEC> {
        I2C_SCLK_EN_W::new(self, 22)
    }
}
#[doc = "I2C_SCLK configuration register\n\nYou can [`read`](crate::Reg::read) this register and get [`i2c_sclk_conf::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`i2c_sclk_conf::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct I2C_SCLK_CONF_SPEC;
impl crate::RegisterSpec for I2C_SCLK_CONF_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`i2c_sclk_conf::R`](R) reader structure"]
impl crate::Readable for I2C_SCLK_CONF_SPEC {}
#[doc = "`write(|w| ..)` method takes [`i2c_sclk_conf::W`](W) writer structure"]
impl crate::Writable for I2C_SCLK_CONF_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets I2C_SCLK_CONF to value 0x0040_0000"]
impl crate::Resettable for I2C_SCLK_CONF_SPEC {
    const RESET_VALUE: u32 = 0x0040_0000;
}
