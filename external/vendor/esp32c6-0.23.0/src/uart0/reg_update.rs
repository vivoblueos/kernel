#[doc = "Register `REG_UPDATE` reader"]
pub type R = crate::R<REG_UPDATE_SPEC>;
#[doc = "Register `REG_UPDATE` writer"]
pub type W = crate::W<REG_UPDATE_SPEC>;
#[doc = "Field `REG_UPDATE` reader - Software write 1 would synchronize registers into UART Core clock domain and would be cleared by hardware after synchronization is done."]
pub type REG_UPDATE_R = crate::BitReader;
#[doc = "Field `REG_UPDATE` writer - Software write 1 would synchronize registers into UART Core clock domain and would be cleared by hardware after synchronization is done."]
pub type REG_UPDATE_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 0 - Software write 1 would synchronize registers into UART Core clock domain and would be cleared by hardware after synchronization is done."]
    #[inline(always)]
    pub fn reg_update(&self) -> REG_UPDATE_R {
        REG_UPDATE_R::new((self.bits & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("REG_UPDATE")
            .field("reg_update", &self.reg_update())
            .finish()
    }
}
impl W {
    #[doc = "Bit 0 - Software write 1 would synchronize registers into UART Core clock domain and would be cleared by hardware after synchronization is done."]
    #[inline(always)]
    pub fn reg_update(&mut self) -> REG_UPDATE_W<'_, REG_UPDATE_SPEC> {
        REG_UPDATE_W::new(self, 0)
    }
}
#[doc = "UART Registers Configuration Update register\n\nYou can [`read`](crate::Reg::read) this register and get [`reg_update::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`reg_update::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct REG_UPDATE_SPEC;
impl crate::RegisterSpec for REG_UPDATE_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`reg_update::R`](R) reader structure"]
impl crate::Readable for REG_UPDATE_SPEC {}
#[doc = "`write(|w| ..)` method takes [`reg_update::W`](W) writer structure"]
impl crate::Writable for REG_UPDATE_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets REG_UPDATE to value 0"]
impl crate::Resettable for REG_UPDATE_SPEC {}
