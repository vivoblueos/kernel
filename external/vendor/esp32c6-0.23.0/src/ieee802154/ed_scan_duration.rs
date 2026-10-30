#[doc = "Register `ED_SCAN_DURATION` reader"]
pub type R = crate::R<ED_SCAN_DURATION_SPEC>;
#[doc = "Register `ED_SCAN_DURATION` writer"]
pub type W = crate::W<ED_SCAN_DURATION_SPEC>;
#[doc = "Field `ED_SCAN_DURATION` reader - "]
pub type ED_SCAN_DURATION_R = crate::FieldReader<u32>;
#[doc = "Field `ED_SCAN_DURATION` writer - "]
pub type ED_SCAN_DURATION_W<'a, REG> = crate::FieldWriter<'a, REG, 24, u32>;
#[doc = "Field `ED_SCAN_WAIT_DLY` reader - "]
pub type ED_SCAN_WAIT_DLY_R = crate::FieldReader;
#[doc = "Field `ED_SCAN_WAIT_DLY` writer - "]
pub type ED_SCAN_WAIT_DLY_W<'a, REG> = crate::FieldWriter<'a, REG, 4>;
impl R {
    #[doc = "Bits 0:23"]
    #[inline(always)]
    pub fn ed_scan_duration(&self) -> ED_SCAN_DURATION_R {
        ED_SCAN_DURATION_R::new(self.bits & 0x00ff_ffff)
    }
    #[doc = "Bits 24:27"]
    #[inline(always)]
    pub fn ed_scan_wait_dly(&self) -> ED_SCAN_WAIT_DLY_R {
        ED_SCAN_WAIT_DLY_R::new(((self.bits >> 24) & 0x0f) as u8)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("ED_SCAN_DURATION")
            .field("ed_scan_duration", &self.ed_scan_duration())
            .field("ed_scan_wait_dly", &self.ed_scan_wait_dly())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:23"]
    #[inline(always)]
    pub fn ed_scan_duration(&mut self) -> ED_SCAN_DURATION_W<'_, ED_SCAN_DURATION_SPEC> {
        ED_SCAN_DURATION_W::new(self, 0)
    }
    #[doc = "Bits 24:27"]
    #[inline(always)]
    pub fn ed_scan_wait_dly(&mut self) -> ED_SCAN_WAIT_DLY_W<'_, ED_SCAN_DURATION_SPEC> {
        ED_SCAN_WAIT_DLY_W::new(self, 24)
    }
}
#[doc = "\n\nYou can [`read`](crate::Reg::read) this register and get [`ed_scan_duration::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`ed_scan_duration::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct ED_SCAN_DURATION_SPEC;
impl crate::RegisterSpec for ED_SCAN_DURATION_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`ed_scan_duration::R`](R) reader structure"]
impl crate::Readable for ED_SCAN_DURATION_SPEC {}
#[doc = "`write(|w| ..)` method takes [`ed_scan_duration::W`](W) writer structure"]
impl crate::Writable for ED_SCAN_DURATION_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets ED_SCAN_DURATION to value 0"]
impl crate::Resettable for ED_SCAN_DURATION_SPEC {}
