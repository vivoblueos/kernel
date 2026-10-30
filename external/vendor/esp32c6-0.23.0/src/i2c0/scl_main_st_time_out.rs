#[doc = "Register `SCL_MAIN_ST_TIME_OUT` reader"]
pub type R = crate::R<SCL_MAIN_ST_TIME_OUT_SPEC>;
#[doc = "Register `SCL_MAIN_ST_TIME_OUT` writer"]
pub type W = crate::W<SCL_MAIN_ST_TIME_OUT_SPEC>;
#[doc = "Field `SCL_MAIN_ST_TO` reader - The threshold value of SCL_MAIN_FSM state unchanged period.nIt should be o more than 23"]
pub type SCL_MAIN_ST_TO_R = crate::FieldReader;
#[doc = "Field `SCL_MAIN_ST_TO` writer - The threshold value of SCL_MAIN_FSM state unchanged period.nIt should be o more than 23"]
pub type SCL_MAIN_ST_TO_W<'a, REG> = crate::FieldWriter<'a, REG, 5>;
impl R {
    #[doc = "Bits 0:4 - The threshold value of SCL_MAIN_FSM state unchanged period.nIt should be o more than 23"]
    #[inline(always)]
    pub fn scl_main_st_to(&self) -> SCL_MAIN_ST_TO_R {
        SCL_MAIN_ST_TO_R::new((self.bits & 0x1f) as u8)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("SCL_MAIN_ST_TIME_OUT")
            .field("scl_main_st_to", &self.scl_main_st_to())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:4 - The threshold value of SCL_MAIN_FSM state unchanged period.nIt should be o more than 23"]
    #[inline(always)]
    pub fn scl_main_st_to(&mut self) -> SCL_MAIN_ST_TO_W<'_, SCL_MAIN_ST_TIME_OUT_SPEC> {
        SCL_MAIN_ST_TO_W::new(self, 0)
    }
}
#[doc = "SCL main status time out register\n\nYou can [`read`](crate::Reg::read) this register and get [`scl_main_st_time_out::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`scl_main_st_time_out::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct SCL_MAIN_ST_TIME_OUT_SPEC;
impl crate::RegisterSpec for SCL_MAIN_ST_TIME_OUT_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`scl_main_st_time_out::R`](R) reader structure"]
impl crate::Readable for SCL_MAIN_ST_TIME_OUT_SPEC {}
#[doc = "`write(|w| ..)` method takes [`scl_main_st_time_out::W`](W) writer structure"]
impl crate::Writable for SCL_MAIN_ST_TIME_OUT_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets SCL_MAIN_ST_TIME_OUT to value 0x10"]
impl crate::Resettable for SCL_MAIN_ST_TIME_OUT_SPEC {
    const RESET_VALUE: u32 = 0x10;
}
