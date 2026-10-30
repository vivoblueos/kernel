#[doc = "Register `I2C%s_CTRL1` reader"]
pub type R = crate::R<I2C_CTRL1_SPEC>;
#[doc = "Register `I2C%s_CTRL1` writer"]
pub type W = crate::W<I2C_CTRL1_SPEC>;
#[doc = "Field `SCL_PULSE_DUR` reader - Configures the duration of the high-level period of the SCL driven by I2C0"]
pub type SCL_PULSE_DUR_R = crate::FieldReader;
#[doc = "Field `SCL_PULSE_DUR` writer - Configures the duration of the high-level period of the SCL driven by I2C0"]
pub type SCL_PULSE_DUR_W<'a, REG> = crate::FieldWriter<'a, REG, 6>;
#[doc = "Field `SDA_SIDE_GUARD` reader - Configures the duration of the low-level period of the SCL driven by I2C0"]
pub type SDA_SIDE_GUARD_R = crate::FieldReader;
#[doc = "Field `SDA_SIDE_GUARD` writer - Configures the duration of the low-level period of the SCL driven by I2C0"]
pub type SDA_SIDE_GUARD_W<'a, REG> = crate::FieldWriter<'a, REG, 5>;
impl R {
    #[doc = "Bits 0:5 - Configures the duration of the high-level period of the SCL driven by I2C0"]
    #[inline(always)]
    pub fn scl_pulse_dur(&self) -> SCL_PULSE_DUR_R {
        SCL_PULSE_DUR_R::new((self.bits & 0x3f) as u8)
    }
    #[doc = "Bits 6:10 - Configures the duration of the low-level period of the SCL driven by I2C0"]
    #[inline(always)]
    pub fn sda_side_guard(&self) -> SDA_SIDE_GUARD_R {
        SDA_SIDE_GUARD_R::new(((self.bits >> 6) & 0x1f) as u8)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("I2C_CTRL1")
            .field("scl_pulse_dur", &self.scl_pulse_dur())
            .field("sda_side_guard", &self.sda_side_guard())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:5 - Configures the duration of the high-level period of the SCL driven by I2C0"]
    #[inline(always)]
    pub fn scl_pulse_dur(&mut self) -> SCL_PULSE_DUR_W<'_, I2C_CTRL1_SPEC> {
        SCL_PULSE_DUR_W::new(self, 0)
    }
    #[doc = "Bits 6:10 - Configures the duration of the low-level period of the SCL driven by I2C0"]
    #[inline(always)]
    pub fn sda_side_guard(&mut self) -> SDA_SIDE_GUARD_W<'_, I2C_CTRL1_SPEC> {
        SDA_SIDE_GUARD_W::new(self, 6)
    }
}
#[doc = "I2C%s_CTRL1 register\n\nYou can [`read`](crate::Reg::read) this register and get [`i2c_ctrl1::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`i2c_ctrl1::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct I2C_CTRL1_SPEC;
impl crate::RegisterSpec for I2C_CTRL1_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`i2c_ctrl1::R`](R) reader structure"]
impl crate::Readable for I2C_CTRL1_SPEC {}
#[doc = "`write(|w| ..)` method takes [`i2c_ctrl1::W`](W) writer structure"]
impl crate::Writable for I2C_CTRL1_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets I2C%s_CTRL1 to value 0x42"]
impl crate::Resettable for I2C_CTRL1_SPEC {
    const RESET_VALUE: u32 = 0x42;
}
