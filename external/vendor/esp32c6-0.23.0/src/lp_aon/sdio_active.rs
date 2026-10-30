#[doc = "Register `SDIO_ACTIVE` reader"]
pub type R = crate::R<SDIO_ACTIVE_SPEC>;
#[doc = "Register `SDIO_ACTIVE` writer"]
pub type W = crate::W<SDIO_ACTIVE_SPEC>;
#[doc = "Field `SDIO_ACT_DNUM` reader - need_des"]
pub type SDIO_ACT_DNUM_R = crate::FieldReader<u16>;
#[doc = "Field `SDIO_ACT_DNUM` writer - need_des"]
pub type SDIO_ACT_DNUM_W<'a, REG> = crate::FieldWriter<'a, REG, 10, u16>;
impl R {
    #[doc = "Bits 22:31 - need_des"]
    #[inline(always)]
    pub fn sdio_act_dnum(&self) -> SDIO_ACT_DNUM_R {
        SDIO_ACT_DNUM_R::new(((self.bits >> 22) & 0x03ff) as u16)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("SDIO_ACTIVE")
            .field("sdio_act_dnum", &self.sdio_act_dnum())
            .finish()
    }
}
impl W {
    #[doc = "Bits 22:31 - need_des"]
    #[inline(always)]
    pub fn sdio_act_dnum(&mut self) -> SDIO_ACT_DNUM_W<'_, SDIO_ACTIVE_SPEC> {
        SDIO_ACT_DNUM_W::new(self, 22)
    }
}
#[doc = "need_des\n\nYou can [`read`](crate::Reg::read) this register and get [`sdio_active::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`sdio_active::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct SDIO_ACTIVE_SPEC;
impl crate::RegisterSpec for SDIO_ACTIVE_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`sdio_active::R`](R) reader structure"]
impl crate::Readable for SDIO_ACTIVE_SPEC {}
#[doc = "`write(|w| ..)` method takes [`sdio_active::W`](W) writer structure"]
impl crate::Writable for SDIO_ACTIVE_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets SDIO_ACTIVE to value 0x0280_0000"]
impl crate::Resettable for SDIO_ACTIVE_SPEC {
    const RESET_VALUE: u32 = 0x0280_0000;
}
