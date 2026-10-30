#[doc = "Register `SCL_ST_TIME_OUT` reader"]
pub type R = crate::R<SCL_ST_TIME_OUT_SPEC>;
#[doc = "Register `SCL_ST_TIME_OUT` writer"]
pub type W = crate::W<SCL_ST_TIME_OUT_SPEC>;
#[doc = "Field `SCL_ST_TO_I2C` reader - The threshold value of SCL_FSM state unchanged period. It should be o more than 23"]
pub type SCL_ST_TO_I2C_R = crate::FieldReader;
#[doc = "Field `SCL_ST_TO_I2C` writer - The threshold value of SCL_FSM state unchanged period. It should be o more than 23"]
pub type SCL_ST_TO_I2C_W<'a, REG> = crate::FieldWriter<'a, REG, 5>;
impl R {
    #[doc = "Bits 0:4 - The threshold value of SCL_FSM state unchanged period. It should be o more than 23"]
    #[inline(always)]
    pub fn scl_st_to_i2c(&self) -> SCL_ST_TO_I2C_R {
        SCL_ST_TO_I2C_R::new((self.bits & 0x1f) as u8)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("SCL_ST_TIME_OUT")
            .field("scl_st_to_i2c", &self.scl_st_to_i2c())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:4 - The threshold value of SCL_FSM state unchanged period. It should be o more than 23"]
    #[inline(always)]
    pub fn scl_st_to_i2c(&mut self) -> SCL_ST_TO_I2C_W<'_, SCL_ST_TIME_OUT_SPEC> {
        SCL_ST_TO_I2C_W::new(self, 0)
    }
}
#[doc = "SCL status time out register\n\nYou can [`read`](crate::Reg::read) this register and get [`scl_st_time_out::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`scl_st_time_out::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct SCL_ST_TIME_OUT_SPEC;
impl crate::RegisterSpec for SCL_ST_TIME_OUT_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`scl_st_time_out::R`](R) reader structure"]
impl crate::Readable for SCL_ST_TIME_OUT_SPEC {}
#[doc = "`write(|w| ..)` method takes [`scl_st_time_out::W`](W) writer structure"]
impl crate::Writable for SCL_ST_TIME_OUT_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets SCL_ST_TIME_OUT to value 0x10"]
impl crate::Resettable for SCL_ST_TIME_OUT_SPEC {
    const RESET_VALUE: u32 = 0x10;
}
