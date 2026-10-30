#[doc = "Register `OPTION1` reader"]
pub type R = crate::R<OPTION1_SPEC>;
#[doc = "Register `OPTION1` writer"]
pub type W = crate::W<OPTION1_SPEC>;
#[doc = "Field `FORCE_DOWNLOAD_BOOT` reader - force chip entry download mode"]
pub type FORCE_DOWNLOAD_BOOT_R = crate::BitReader;
#[doc = "Field `FORCE_DOWNLOAD_BOOT` writer - force chip entry download mode"]
pub type FORCE_DOWNLOAD_BOOT_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 0 - force chip entry download mode"]
    #[inline(always)]
    pub fn force_download_boot(&self) -> FORCE_DOWNLOAD_BOOT_R {
        FORCE_DOWNLOAD_BOOT_R::new((self.bits & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("OPTION1")
            .field("force_download_boot", &self.force_download_boot())
            .finish()
    }
}
impl W {
    #[doc = "Bit 0 - force chip entry download mode"]
    #[inline(always)]
    pub fn force_download_boot(&mut self) -> FORCE_DOWNLOAD_BOOT_W<'_, OPTION1_SPEC> {
        FORCE_DOWNLOAD_BOOT_W::new(self, 0)
    }
}
#[doc = "rtc configure register\n\nYou can [`read`](crate::Reg::read) this register and get [`option1::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`option1::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct OPTION1_SPEC;
impl crate::RegisterSpec for OPTION1_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`option1::R`](R) reader structure"]
impl crate::Readable for OPTION1_SPEC {}
#[doc = "`write(|w| ..)` method takes [`option1::W`](W) writer structure"]
impl crate::Writable for OPTION1_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets OPTION1 to value 0"]
impl crate::Resettable for OPTION1_SPEC {}
