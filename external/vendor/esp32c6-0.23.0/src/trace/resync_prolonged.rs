#[doc = "Register `RESYNC_PROLONGED` reader"]
pub type R = crate::R<RESYNC_PROLONGED_SPEC>;
#[doc = "Register `RESYNC_PROLONGED` writer"]
pub type W = crate::W<RESYNC_PROLONGED_SPEC>;
#[doc = "Field `RESYNC_PROLONGED` reader - count number, when count to this value, send a sync package"]
pub type RESYNC_PROLONGED_R = crate::FieldReader<u32>;
#[doc = "Field `RESYNC_PROLONGED` writer - count number, when count to this value, send a sync package"]
pub type RESYNC_PROLONGED_W<'a, REG> = crate::FieldWriter<'a, REG, 24, u32>;
#[doc = "Field `RESYNC_MODE` reader - resyc mode sel: 0: default, cycle count 1: package num count"]
pub type RESYNC_MODE_R = crate::BitReader;
#[doc = "Field `RESYNC_MODE` writer - resyc mode sel: 0: default, cycle count 1: package num count"]
pub type RESYNC_MODE_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bits 0:23 - count number, when count to this value, send a sync package"]
    #[inline(always)]
    pub fn resync_prolonged(&self) -> RESYNC_PROLONGED_R {
        RESYNC_PROLONGED_R::new(self.bits & 0x00ff_ffff)
    }
    #[doc = "Bit 24 - resyc mode sel: 0: default, cycle count 1: package num count"]
    #[inline(always)]
    pub fn resync_mode(&self) -> RESYNC_MODE_R {
        RESYNC_MODE_R::new(((self.bits >> 24) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("RESYNC_PROLONGED")
            .field("resync_prolonged", &self.resync_prolonged())
            .field("resync_mode", &self.resync_mode())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:23 - count number, when count to this value, send a sync package"]
    #[inline(always)]
    pub fn resync_prolonged(&mut self) -> RESYNC_PROLONGED_W<'_, RESYNC_PROLONGED_SPEC> {
        RESYNC_PROLONGED_W::new(self, 0)
    }
    #[doc = "Bit 24 - resyc mode sel: 0: default, cycle count 1: package num count"]
    #[inline(always)]
    pub fn resync_mode(&mut self) -> RESYNC_MODE_W<'_, RESYNC_PROLONGED_SPEC> {
        RESYNC_MODE_W::new(self, 24)
    }
}
#[doc = "resync configuration register\n\nYou can [`read`](crate::Reg::read) this register and get [`resync_prolonged::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`resync_prolonged::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct RESYNC_PROLONGED_SPEC;
impl crate::RegisterSpec for RESYNC_PROLONGED_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`resync_prolonged::R`](R) reader structure"]
impl crate::Readable for RESYNC_PROLONGED_SPEC {}
#[doc = "`write(|w| ..)` method takes [`resync_prolonged::W`](W) writer structure"]
impl crate::Writable for RESYNC_PROLONGED_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets RESYNC_PROLONGED to value 0x80"]
impl crate::Resettable for RESYNC_PROLONGED_SPEC {
    const RESET_VALUE: u32 = 0x80;
}
