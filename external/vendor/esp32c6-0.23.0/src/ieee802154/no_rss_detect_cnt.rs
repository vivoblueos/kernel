#[doc = "Register `NO_RSS_DETECT_CNT` reader"]
pub type R = crate::R<NO_RSS_DETECT_CNT_SPEC>;
#[doc = "Register `NO_RSS_DETECT_CNT` writer"]
pub type W = crate::W<NO_RSS_DETECT_CNT_SPEC>;
#[doc = "Field `NO_RSS_DETECT_CNT` reader - "]
pub type NO_RSS_DETECT_CNT_R = crate::FieldReader<u16>;
#[doc = "Field `NO_RSS_DETECT_CNT` writer - "]
pub type NO_RSS_DETECT_CNT_W<'a, REG> = crate::FieldWriter<'a, REG, 16, u16>;
impl R {
    #[doc = "Bits 0:15"]
    #[inline(always)]
    pub fn no_rss_detect_cnt(&self) -> NO_RSS_DETECT_CNT_R {
        NO_RSS_DETECT_CNT_R::new((self.bits & 0xffff) as u16)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("NO_RSS_DETECT_CNT")
            .field("no_rss_detect_cnt", &self.no_rss_detect_cnt())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:15"]
    #[inline(always)]
    pub fn no_rss_detect_cnt(&mut self) -> NO_RSS_DETECT_CNT_W<'_, NO_RSS_DETECT_CNT_SPEC> {
        NO_RSS_DETECT_CNT_W::new(self, 0)
    }
}
#[doc = "\n\nYou can [`read`](crate::Reg::read) this register and get [`no_rss_detect_cnt::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`no_rss_detect_cnt::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct NO_RSS_DETECT_CNT_SPEC;
impl crate::RegisterSpec for NO_RSS_DETECT_CNT_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`no_rss_detect_cnt::R`](R) reader structure"]
impl crate::Readable for NO_RSS_DETECT_CNT_SPEC {}
#[doc = "`write(|w| ..)` method takes [`no_rss_detect_cnt::W`](W) writer structure"]
impl crate::Writable for NO_RSS_DETECT_CNT_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets NO_RSS_DETECT_CNT to value 0"]
impl crate::Resettable for NO_RSS_DETECT_CNT_SPEC {}
