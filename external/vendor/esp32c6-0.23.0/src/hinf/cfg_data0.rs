#[doc = "Register `CFG_DATA0` reader"]
pub type R = crate::R<CFG_DATA0_SPEC>;
#[doc = "Register `CFG_DATA0` writer"]
pub type W = crate::W<CFG_DATA0_SPEC>;
#[doc = "Field `DEVICE_ID_FN1` reader - configure device id of function1 in cis"]
pub type DEVICE_ID_FN1_R = crate::FieldReader<u16>;
#[doc = "Field `DEVICE_ID_FN1` writer - configure device id of function1 in cis"]
pub type DEVICE_ID_FN1_W<'a, REG> = crate::FieldWriter<'a, REG, 16, u16>;
#[doc = "Field `USER_ID_FN1` reader - configure user id of function1 in cis"]
pub type USER_ID_FN1_R = crate::FieldReader<u16>;
#[doc = "Field `USER_ID_FN1` writer - configure user id of function1 in cis"]
pub type USER_ID_FN1_W<'a, REG> = crate::FieldWriter<'a, REG, 16, u16>;
impl R {
    #[doc = "Bits 0:15 - configure device id of function1 in cis"]
    #[inline(always)]
    pub fn device_id_fn1(&self) -> DEVICE_ID_FN1_R {
        DEVICE_ID_FN1_R::new((self.bits & 0xffff) as u16)
    }
    #[doc = "Bits 16:31 - configure user id of function1 in cis"]
    #[inline(always)]
    pub fn user_id_fn1(&self) -> USER_ID_FN1_R {
        USER_ID_FN1_R::new(((self.bits >> 16) & 0xffff) as u16)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("CFG_DATA0")
            .field("device_id_fn1", &self.device_id_fn1())
            .field("user_id_fn1", &self.user_id_fn1())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:15 - configure device id of function1 in cis"]
    #[inline(always)]
    pub fn device_id_fn1(&mut self) -> DEVICE_ID_FN1_W<'_, CFG_DATA0_SPEC> {
        DEVICE_ID_FN1_W::new(self, 0)
    }
    #[doc = "Bits 16:31 - configure user id of function1 in cis"]
    #[inline(always)]
    pub fn user_id_fn1(&mut self) -> USER_ID_FN1_W<'_, CFG_DATA0_SPEC> {
        USER_ID_FN1_W::new(self, 16)
    }
}
#[doc = "Configure sdio cis content\n\nYou can [`read`](crate::Reg::read) this register and get [`cfg_data0::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`cfg_data0::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct CFG_DATA0_SPEC;
impl crate::RegisterSpec for CFG_DATA0_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`cfg_data0::R`](R) reader structure"]
impl crate::Readable for CFG_DATA0_SPEC {}
#[doc = "`write(|w| ..)` method takes [`cfg_data0::W`](W) writer structure"]
impl crate::Writable for CFG_DATA0_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets CFG_DATA0 to value 0x0092_6666"]
impl crate::Resettable for CFG_DATA0_SPEC {
    const RESET_VALUE: u32 = 0x0092_6666;
}
