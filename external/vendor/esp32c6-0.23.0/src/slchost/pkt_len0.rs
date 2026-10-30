#[doc = "Register `PKT_LEN0` reader"]
pub type R = crate::R<PKT_LEN0_SPEC>;
#[doc = "Field `HOSTSLCHOST_SLC0_LEN0` reader - *******Description***********"]
pub type HOSTSLCHOST_SLC0_LEN0_R = crate::FieldReader<u32>;
#[doc = "Field `HOSTSLCHOST_SLC0_LEN0_CHECK` reader - *******Description***********"]
pub type HOSTSLCHOST_SLC0_LEN0_CHECK_R = crate::FieldReader<u16>;
impl R {
    #[doc = "Bits 0:19 - *******Description***********"]
    #[inline(always)]
    pub fn hostslchost_slc0_len0(&self) -> HOSTSLCHOST_SLC0_LEN0_R {
        HOSTSLCHOST_SLC0_LEN0_R::new(self.bits & 0x000f_ffff)
    }
    #[doc = "Bits 20:31 - *******Description***********"]
    #[inline(always)]
    pub fn hostslchost_slc0_len0_check(&self) -> HOSTSLCHOST_SLC0_LEN0_CHECK_R {
        HOSTSLCHOST_SLC0_LEN0_CHECK_R::new(((self.bits >> 20) & 0x0fff) as u16)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("PKT_LEN0")
            .field("hostslchost_slc0_len0", &self.hostslchost_slc0_len0())
            .field(
                "hostslchost_slc0_len0_check",
                &self.hostslchost_slc0_len0_check(),
            )
            .finish()
    }
}
#[doc = "*******Description***********\n\nYou can [`read`](crate::Reg::read) this register and get [`pkt_len0::R`](R). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct PKT_LEN0_SPEC;
impl crate::RegisterSpec for PKT_LEN0_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`pkt_len0::R`](R) reader structure"]
impl crate::Readable for PKT_LEN0_SPEC {}
#[doc = "`reset()` method sets PKT_LEN0 to value 0"]
impl crate::Resettable for PKT_LEN0_SPEC {}
