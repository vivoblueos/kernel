#[doc = "Register `DESTINATION` reader"]
pub type R = crate::R<DESTINATION_SPEC>;
#[doc = "Register `DESTINATION` writer"]
pub type W = crate::W<DESTINATION_SPEC>;
#[doc = "Field `DESTINATION` reader - This bit stores the destination. 0: flash(default). 1: reserved."]
pub type DESTINATION_R = crate::BitReader;
#[doc = "Field `DESTINATION` writer - This bit stores the destination. 0: flash(default). 1: reserved."]
pub type DESTINATION_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 0 - This bit stores the destination. 0: flash(default). 1: reserved."]
    #[inline(always)]
    pub fn destination(&self) -> DESTINATION_R {
        DESTINATION_R::new((self.bits & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("DESTINATION")
            .field("destination", &self.destination())
            .finish()
    }
}
impl W {
    #[doc = "Bit 0 - This bit stores the destination. 0: flash(default). 1: reserved."]
    #[inline(always)]
    pub fn destination(&mut self) -> DESTINATION_W<'_, DESTINATION_SPEC> {
        DESTINATION_W::new(self, 0)
    }
}
#[doc = "XTS-AES destination register\n\nYou can [`read`](crate::Reg::read) this register and get [`destination::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`destination::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct DESTINATION_SPEC;
impl crate::RegisterSpec for DESTINATION_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`destination::R`](R) reader structure"]
impl crate::Readable for DESTINATION_SPEC {}
#[doc = "`write(|w| ..)` method takes [`destination::W`](W) writer structure"]
impl crate::Writable for DESTINATION_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets DESTINATION to value 0"]
impl crate::Resettable for DESTINATION_SPEC {}
