#[doc = "Register `APB2OTP_EN` reader"]
pub type R = crate::R<APB2OTP_EN_SPEC>;
#[doc = "Register `APB2OTP_EN` writer"]
pub type W = crate::W<APB2OTP_EN_SPEC>;
#[doc = "Field `APB2OTP_EN` reader - Debug mode enable signal."]
pub type APB2OTP_EN_R = crate::BitReader;
#[doc = "Field `APB2OTP_EN` writer - Debug mode enable signal."]
pub type APB2OTP_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 0 - Debug mode enable signal."]
    #[inline(always)]
    pub fn apb2otp_en(&self) -> APB2OTP_EN_R {
        APB2OTP_EN_R::new((self.bits & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("APB2OTP_EN")
            .field("apb2otp_en", &self.apb2otp_en())
            .finish()
    }
}
impl W {
    #[doc = "Bit 0 - Debug mode enable signal."]
    #[inline(always)]
    pub fn apb2otp_en(&mut self) -> APB2OTP_EN_W<'_, APB2OTP_EN_SPEC> {
        APB2OTP_EN_W::new(self, 0)
    }
}
#[doc = "Otp_debuger apb2otp enable configuration register.\n\nYou can [`read`](crate::Reg::read) this register and get [`apb2otp_en::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`apb2otp_en::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct APB2OTP_EN_SPEC;
impl crate::RegisterSpec for APB2OTP_EN_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`apb2otp_en::R`](R) reader structure"]
impl crate::Readable for APB2OTP_EN_SPEC {}
#[doc = "`write(|w| ..)` method takes [`apb2otp_en::W`](W) writer structure"]
impl crate::Writable for APB2OTP_EN_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets APB2OTP_EN to value 0"]
impl crate::Resettable for APB2OTP_EN_SPEC {}
