#[doc = "Register `ED_SCAN_COEX_CNT` reader"]
pub type R = crate::R<ED_SCAN_COEX_CNT_SPEC>;
#[doc = "Register `ED_SCAN_COEX_CNT` writer"]
pub type W = crate::W<ED_SCAN_COEX_CNT_SPEC>;
#[doc = "Field `ED_SCAN_COEX_CNT` reader - "]
pub type ED_SCAN_COEX_CNT_R = crate::FieldReader<u16>;
#[doc = "Field `ED_SCAN_COEX_CNT` writer - "]
pub type ED_SCAN_COEX_CNT_W<'a, REG> = crate::FieldWriter<'a, REG, 16, u16>;
impl R {
    #[doc = "Bits 0:15"]
    #[inline(always)]
    pub fn ed_scan_coex_cnt(&self) -> ED_SCAN_COEX_CNT_R {
        ED_SCAN_COEX_CNT_R::new((self.bits & 0xffff) as u16)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("ED_SCAN_COEX_CNT")
            .field("ed_scan_coex_cnt", &self.ed_scan_coex_cnt())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:15"]
    #[inline(always)]
    pub fn ed_scan_coex_cnt(&mut self) -> ED_SCAN_COEX_CNT_W<'_, ED_SCAN_COEX_CNT_SPEC> {
        ED_SCAN_COEX_CNT_W::new(self, 0)
    }
}
#[doc = "\n\nYou can [`read`](crate::Reg::read) this register and get [`ed_scan_coex_cnt::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`ed_scan_coex_cnt::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct ED_SCAN_COEX_CNT_SPEC;
impl crate::RegisterSpec for ED_SCAN_COEX_CNT_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`ed_scan_coex_cnt::R`](R) reader structure"]
impl crate::Readable for ED_SCAN_COEX_CNT_SPEC {}
#[doc = "`write(|w| ..)` method takes [`ed_scan_coex_cnt::W`](W) writer structure"]
impl crate::Writable for ED_SCAN_COEX_CNT_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets ED_SCAN_COEX_CNT to value 0"]
impl crate::Resettable for ED_SCAN_COEX_CNT_SPEC {}
