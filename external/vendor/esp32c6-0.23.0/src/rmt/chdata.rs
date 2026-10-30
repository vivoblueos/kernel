#[doc = "Register `CH%sDATA` reader"]
pub type R = crate::R<CHDATA_SPEC>;
#[doc = "Register `CH%sDATA` writer"]
pub type W = crate::W<CHDATA_SPEC>;
#[doc = "Field `DATA` reader - Read and write data for channel %s via APB FIFO."]
pub type DATA_R = crate::FieldReader<u32>;
#[doc = "Field `DATA` writer - Read and write data for channel %s via APB FIFO."]
pub type DATA_W<'a, REG> = crate::FieldWriter<'a, REG, 32, u32>;
impl R {
    #[doc = "Bits 0:31 - Read and write data for channel %s via APB FIFO."]
    #[inline(always)]
    pub fn data(&self) -> DATA_R {
        DATA_R::new(self.bits)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("CHDATA")
            .field("data", &self.data())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:31 - Read and write data for channel %s via APB FIFO."]
    #[inline(always)]
    pub fn data(&mut self) -> DATA_W<'_, CHDATA_SPEC> {
        DATA_W::new(self, 0)
    }
}
#[doc = "The read and write data register for CHANNEL%s by apb fifo access.\n\nYou can [`read`](crate::Reg::read) this register and get [`chdata::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`chdata::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct CHDATA_SPEC;
impl crate::RegisterSpec for CHDATA_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`chdata::R`](R) reader structure"]
impl crate::Readable for CHDATA_SPEC {}
#[doc = "`write(|w| ..)` method takes [`chdata::W`](W) writer structure"]
impl crate::Writable for CHDATA_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets CH%sDATA to value 0"]
impl crate::Resettable for CHDATA_SPEC {}
