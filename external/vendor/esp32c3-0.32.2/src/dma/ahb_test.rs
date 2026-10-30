#[doc = "Register `AHB_TEST` reader"]
pub type R = crate::R<AHB_TEST_SPEC>;
#[doc = "Register `AHB_TEST` writer"]
pub type W = crate::W<AHB_TEST_SPEC>;
#[doc = "Field `AHB_TESTMODE` reader - reserved"]
pub type AHB_TESTMODE_R = crate::FieldReader;
#[doc = "Field `AHB_TESTMODE` writer - reserved"]
pub type AHB_TESTMODE_W<'a, REG> = crate::FieldWriter<'a, REG, 3>;
#[doc = "Field `AHB_TESTADDR` reader - reserved"]
pub type AHB_TESTADDR_R = crate::FieldReader;
#[doc = "Field `AHB_TESTADDR` writer - reserved"]
pub type AHB_TESTADDR_W<'a, REG> = crate::FieldWriter<'a, REG, 2>;
impl R {
    #[doc = "Bits 0:2 - reserved"]
    #[inline(always)]
    pub fn ahb_testmode(&self) -> AHB_TESTMODE_R {
        AHB_TESTMODE_R::new((self.bits & 7) as u8)
    }
    #[doc = "Bits 4:5 - reserved"]
    #[inline(always)]
    pub fn ahb_testaddr(&self) -> AHB_TESTADDR_R {
        AHB_TESTADDR_R::new(((self.bits >> 4) & 3) as u8)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("AHB_TEST")
            .field("ahb_testmode", &self.ahb_testmode())
            .field("ahb_testaddr", &self.ahb_testaddr())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:2 - reserved"]
    #[inline(always)]
    pub fn ahb_testmode(&mut self) -> AHB_TESTMODE_W<'_, AHB_TEST_SPEC> {
        AHB_TESTMODE_W::new(self, 0)
    }
    #[doc = "Bits 4:5 - reserved"]
    #[inline(always)]
    pub fn ahb_testaddr(&mut self) -> AHB_TESTADDR_W<'_, AHB_TEST_SPEC> {
        AHB_TESTADDR_W::new(self, 4)
    }
}
#[doc = "DMA_AHB_TEST_REG.\n\nYou can [`read`](crate::Reg::read) this register and get [`ahb_test::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`ahb_test::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct AHB_TEST_SPEC;
impl crate::RegisterSpec for AHB_TEST_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`ahb_test::R`](R) reader structure"]
impl crate::Readable for AHB_TEST_SPEC {}
#[doc = "`write(|w| ..)` method takes [`ahb_test::W`](W) writer structure"]
impl crate::Writable for AHB_TEST_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets AHB_TEST to value 0"]
impl crate::Resettable for AHB_TEST_SPEC {}
