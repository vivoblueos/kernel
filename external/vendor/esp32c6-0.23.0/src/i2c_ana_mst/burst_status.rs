#[doc = "Register `BURST_STATUS` reader"]
pub type R = crate::R<BURST_STATUS_SPEC>;
#[doc = "Register `BURST_STATUS` writer"]
pub type W = crate::W<BURST_STATUS_SPEC>;
#[doc = "Field `MST_BURST_DONE` reader - ?"]
pub type MST_BURST_DONE_R = crate::BitReader;
#[doc = "Field `MST0_BURST_ERR` reader - ?"]
pub type MST0_BURST_ERR_R = crate::BitReader;
#[doc = "Field `MST1_BURST_ERR` reader - ?"]
pub type MST1_BURST_ERR_R = crate::BitReader;
#[doc = "Field `TIMEOUT_CNT` reader - ?"]
pub type TIMEOUT_CNT_R = crate::FieldReader<u32>;
impl R {
    #[doc = "Bit 0 - ?"]
    #[inline(always)]
    pub fn mst_burst_done(&self) -> MST_BURST_DONE_R {
        MST_BURST_DONE_R::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - ?"]
    #[inline(always)]
    pub fn mst0_burst_err(&self) -> MST0_BURST_ERR_R {
        MST0_BURST_ERR_R::new(((self.bits >> 1) & 1) != 0)
    }
    #[doc = "Bit 2 - ?"]
    #[inline(always)]
    pub fn mst1_burst_err(&self) -> MST1_BURST_ERR_R {
        MST1_BURST_ERR_R::new(((self.bits >> 2) & 1) != 0)
    }
    #[doc = "Bits 3:19 - ?"]
    #[inline(always)]
    pub fn timeout_cnt(&self) -> TIMEOUT_CNT_R {
        TIMEOUT_CNT_R::new((self.bits >> 3) & 0x0001_ffff)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("BURST_STATUS")
            .field("mst_burst_done", &self.mst_burst_done())
            .field("mst0_burst_err", &self.mst0_burst_err())
            .field("mst1_burst_err", &self.mst1_burst_err())
            .field("timeout_cnt", &self.timeout_cnt())
            .finish()
    }
}
impl W {}
#[doc = "BURST_STATUS register\n\nYou can [`read`](crate::Reg::read) this register and get [`burst_status::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`burst_status::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct BURST_STATUS_SPEC;
impl crate::RegisterSpec for BURST_STATUS_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`burst_status::R`](R) reader structure"]
impl crate::Readable for BURST_STATUS_SPEC {}
#[doc = "`write(|w| ..)` method takes [`burst_status::W`](W) writer structure"]
impl crate::Writable for BURST_STATUS_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets BURST_STATUS to value 0"]
impl crate::Resettable for BURST_STATUS_SPEC {}
