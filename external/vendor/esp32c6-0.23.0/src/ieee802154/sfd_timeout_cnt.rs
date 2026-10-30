#[doc = "Register `SFD_TIMEOUT_CNT` reader"]
pub type R = crate::R<SFD_TIMEOUT_CNT_SPEC>;
#[doc = "Register `SFD_TIMEOUT_CNT` writer"]
pub type W = crate::W<SFD_TIMEOUT_CNT_SPEC>;
#[doc = "Field `SFD_TIMEOUT_CNT` reader - "]
pub type SFD_TIMEOUT_CNT_R = crate::FieldReader<u16>;
#[doc = "Field `SFD_TIMEOUT_CNT` writer - "]
pub type SFD_TIMEOUT_CNT_W<'a, REG> = crate::FieldWriter<'a, REG, 16, u16>;
impl R {
    #[doc = "Bits 0:15"]
    #[inline(always)]
    pub fn sfd_timeout_cnt(&self) -> SFD_TIMEOUT_CNT_R {
        SFD_TIMEOUT_CNT_R::new((self.bits & 0xffff) as u16)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("SFD_TIMEOUT_CNT")
            .field("sfd_timeout_cnt", &self.sfd_timeout_cnt())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:15"]
    #[inline(always)]
    pub fn sfd_timeout_cnt(&mut self) -> SFD_TIMEOUT_CNT_W<'_, SFD_TIMEOUT_CNT_SPEC> {
        SFD_TIMEOUT_CNT_W::new(self, 0)
    }
}
#[doc = "\n\nYou can [`read`](crate::Reg::read) this register and get [`sfd_timeout_cnt::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`sfd_timeout_cnt::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct SFD_TIMEOUT_CNT_SPEC;
impl crate::RegisterSpec for SFD_TIMEOUT_CNT_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`sfd_timeout_cnt::R`](R) reader structure"]
impl crate::Readable for SFD_TIMEOUT_CNT_SPEC {}
#[doc = "`write(|w| ..)` method takes [`sfd_timeout_cnt::W`](W) writer structure"]
impl crate::Writable for SFD_TIMEOUT_CNT_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets SFD_TIMEOUT_CNT to value 0"]
impl crate::Resettable for SFD_TIMEOUT_CNT_SPEC {}
