#[doc = "Register `RND_DATA` reader"]
pub type R = crate::R<RND_DATA_SPEC>;
#[doc = "Field `RND_DATA` reader - reg_rnd_data"]
pub type RND_DATA_R = crate::FieldReader<u32>;
impl R {
    #[doc = "Bits 0:31 - reg_rnd_data"]
    #[inline(always)]
    pub fn rnd_data(&self) -> RND_DATA_R {
        RND_DATA_R::new(self.bits)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("RND_DATA")
            .field("rnd_data", &self.rnd_data())
            .finish()
    }
}
#[doc = "APB_CTRL_RND_DATA_REG\n\nYou can [`read`](crate::Reg::read) this register and get [`rnd_data::R`](R). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct RND_DATA_SPEC;
impl crate::RegisterSpec for RND_DATA_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`rnd_data::R`](R) reader structure"]
impl crate::Readable for RND_DATA_SPEC {}
#[doc = "`reset()` method sets RND_DATA to value 0"]
impl crate::Resettable for RND_DATA_SPEC {}
