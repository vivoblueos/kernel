#[doc = "Register `SAR_PATT_TAB2` reader"]
pub type R = crate::R<SAR_PATT_TAB2_SPEC>;
#[doc = "Register `SAR_PATT_TAB2` writer"]
pub type W = crate::W<SAR_PATT_TAB2_SPEC>;
#[doc = "Field `SAR_PATT_TAB2` reader - Item 4 ~ 7 for pattern table 1 (each item one byte)"]
pub type SAR_PATT_TAB2_R = crate::FieldReader<u32>;
#[doc = "Field `SAR_PATT_TAB2` writer - Item 4 ~ 7 for pattern table 1 (each item one byte)"]
pub type SAR_PATT_TAB2_W<'a, REG> = crate::FieldWriter<'a, REG, 24, u32>;
impl R {
    #[doc = "Bits 0:23 - Item 4 ~ 7 for pattern table 1 (each item one byte)"]
    #[inline(always)]
    pub fn sar_patt_tab2(&self) -> SAR_PATT_TAB2_R {
        SAR_PATT_TAB2_R::new(self.bits & 0x00ff_ffff)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("SAR_PATT_TAB2")
            .field("sar_patt_tab2", &self.sar_patt_tab2())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:23 - Item 4 ~ 7 for pattern table 1 (each item one byte)"]
    #[inline(always)]
    pub fn sar_patt_tab2(&mut self) -> SAR_PATT_TAB2_W<'_, SAR_PATT_TAB2_SPEC> {
        SAR_PATT_TAB2_W::new(self, 0)
    }
}
#[doc = "digital saradc configure register\n\nYou can [`read`](crate::Reg::read) this register and get [`sar_patt_tab2::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`sar_patt_tab2::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct SAR_PATT_TAB2_SPEC;
impl crate::RegisterSpec for SAR_PATT_TAB2_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`sar_patt_tab2::R`](R) reader structure"]
impl crate::Readable for SAR_PATT_TAB2_SPEC {}
#[doc = "`write(|w| ..)` method takes [`sar_patt_tab2::W`](W) writer structure"]
impl crate::Writable for SAR_PATT_TAB2_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets SAR_PATT_TAB2 to value 0"]
impl crate::Resettable for SAR_PATT_TAB2_SPEC {}
