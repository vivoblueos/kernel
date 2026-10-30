#[doc = "Register `IN_CONF1` reader"]
pub type R = crate::R<IN_CONF1_SPEC>;
#[doc = "Register `IN_CONF1` writer"]
pub type W = crate::W<IN_CONF1_SPEC>;
#[doc = "Field `IN_CHECK_OWNER` reader - Set this bit to enable checking the owner attribute of the link descriptor."]
pub type IN_CHECK_OWNER_R = crate::BitReader;
#[doc = "Field `IN_CHECK_OWNER` writer - Set this bit to enable checking the owner attribute of the link descriptor."]
pub type IN_CHECK_OWNER_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 12 - Set this bit to enable checking the owner attribute of the link descriptor."]
    #[inline(always)]
    pub fn in_check_owner(&self) -> IN_CHECK_OWNER_R {
        IN_CHECK_OWNER_R::new(((self.bits >> 12) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("IN_CONF1")
            .field("in_check_owner", &self.in_check_owner())
            .finish()
    }
}
impl W {
    #[doc = "Bit 12 - Set this bit to enable checking the owner attribute of the link descriptor."]
    #[inline(always)]
    pub fn in_check_owner(&mut self) -> IN_CHECK_OWNER_W<'_, IN_CONF1_SPEC> {
        IN_CHECK_OWNER_W::new(self, 12)
    }
}
#[doc = "Configure 1 register of Rx channel 0\n\nYou can [`read`](crate::Reg::read) this register and get [`in_conf1::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`in_conf1::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct IN_CONF1_SPEC;
impl crate::RegisterSpec for IN_CONF1_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`in_conf1::R`](R) reader structure"]
impl crate::Readable for IN_CONF1_SPEC {}
#[doc = "`write(|w| ..)` method takes [`in_conf1::W`](W) writer structure"]
impl crate::Writable for IN_CONF1_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets IN_CONF1 to value 0"]
impl crate::Resettable for IN_CONF1_SPEC {}
