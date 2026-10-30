#[doc = "Register `RETENTION_CFG` reader"]
pub type R = crate::R<RETENTION_CFG_SPEC>;
#[doc = "Register `RETENTION_CFG` writer"]
pub type W = crate::W<RETENTION_CFG_SPEC>;
#[doc = "Field `RET_INV_CFG` reader - retention inv scan out"]
pub type RET_INV_CFG_R = crate::FieldReader<u32>;
#[doc = "Field `RET_INV_CFG` writer - retention inv scan out"]
pub type RET_INV_CFG_W<'a, REG> = crate::FieldWriter<'a, REG, 32, u32>;
impl R {
    #[doc = "Bits 0:31 - retention inv scan out"]
    #[inline(always)]
    pub fn ret_inv_cfg(&self) -> RET_INV_CFG_R {
        RET_INV_CFG_R::new(self.bits)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("RETENTION_CFG")
            .field("ret_inv_cfg", &self.ret_inv_cfg())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:31 - retention inv scan out"]
    #[inline(always)]
    pub fn ret_inv_cfg(&mut self) -> RET_INV_CFG_W<'_, RETENTION_CFG_SPEC> {
        RET_INV_CFG_W::new(self, 0)
    }
}
#[doc = "retention_cfg\n\nYou can [`read`](crate::Reg::read) this register and get [`retention_cfg::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`retention_cfg::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct RETENTION_CFG_SPEC;
impl crate::RegisterSpec for RETENTION_CFG_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`retention_cfg::R`](R) reader structure"]
impl crate::Readable for RETENTION_CFG_SPEC {}
#[doc = "`write(|w| ..)` method takes [`retention_cfg::W`](W) writer structure"]
impl crate::Writable for RETENTION_CFG_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets RETENTION_CFG to value 0xffff_ffff"]
impl crate::Resettable for RETENTION_CFG_SPEC {
    const RESET_VALUE: u32 = 0xffff_ffff;
}
