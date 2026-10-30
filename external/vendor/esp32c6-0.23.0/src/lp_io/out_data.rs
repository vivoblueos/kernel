#[doc = "Register `OUT_DATA` reader"]
pub type R = crate::R<OUT_DATA_SPEC>;
#[doc = "Register `OUT_DATA` writer"]
pub type W = crate::W<OUT_DATA_SPEC>;
#[doc = "Field `OUT_DATA` reader - set lp gpio output data"]
pub type OUT_DATA_R = crate::FieldReader;
#[doc = "Field `OUT_DATA` writer - set lp gpio output data"]
pub type OUT_DATA_W<'a, REG> = crate::FieldWriter<'a, REG, 8>;
impl R {
    #[doc = "Bits 0:7 - set lp gpio output data"]
    #[inline(always)]
    pub fn out_data(&self) -> OUT_DATA_R {
        OUT_DATA_R::new((self.bits & 0xff) as u8)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("OUT_DATA")
            .field("out_data", &self.out_data())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:7 - set lp gpio output data"]
    #[inline(always)]
    pub fn out_data(&mut self) -> OUT_DATA_W<'_, OUT_DATA_SPEC> {
        OUT_DATA_W::new(self, 0)
    }
}
#[doc = "need des\n\nYou can [`read`](crate::Reg::read) this register and get [`out_data::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`out_data::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct OUT_DATA_SPEC;
impl crate::RegisterSpec for OUT_DATA_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`out_data::R`](R) reader structure"]
impl crate::Readable for OUT_DATA_SPEC {}
#[doc = "`write(|w| ..)` method takes [`out_data::W`](W) writer structure"]
impl crate::Writable for OUT_DATA_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets OUT_DATA to value 0"]
impl crate::Resettable for OUT_DATA_SPEC {}
