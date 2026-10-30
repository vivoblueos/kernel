#[doc = "Register `DMA_APBPERI_PMS_MONITOR_3` reader"]
pub type R = crate::R<DMA_APBPERI_PMS_MONITOR_3_SPEC>;
#[doc = "Field `DMA_APBPERI_PMS_MONITOR_VIOLATE_STATUS_WR` reader - dma_apbperi_pms_monitor_violate_status_wr"]
pub type DMA_APBPERI_PMS_MONITOR_VIOLATE_STATUS_WR_R = crate::BitReader;
#[doc = "Field `DMA_APBPERI_PMS_MONITOR_VIOLATE_STATUS_BYTEEN` reader - dma_apbperi_pms_monitor_violate_status_byteen"]
pub type DMA_APBPERI_PMS_MONITOR_VIOLATE_STATUS_BYTEEN_R = crate::FieldReader;
impl R {
    #[doc = "Bit 0 - dma_apbperi_pms_monitor_violate_status_wr"]
    #[inline(always)]
    pub fn dma_apbperi_pms_monitor_violate_status_wr(
        &self,
    ) -> DMA_APBPERI_PMS_MONITOR_VIOLATE_STATUS_WR_R {
        DMA_APBPERI_PMS_MONITOR_VIOLATE_STATUS_WR_R::new((self.bits & 1) != 0)
    }
    #[doc = "Bits 1:4 - dma_apbperi_pms_monitor_violate_status_byteen"]
    #[inline(always)]
    pub fn dma_apbperi_pms_monitor_violate_status_byteen(
        &self,
    ) -> DMA_APBPERI_PMS_MONITOR_VIOLATE_STATUS_BYTEEN_R {
        DMA_APBPERI_PMS_MONITOR_VIOLATE_STATUS_BYTEEN_R::new(((self.bits >> 1) & 0x0f) as u8)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("DMA_APBPERI_PMS_MONITOR_3")
            .field(
                "dma_apbperi_pms_monitor_violate_status_wr",
                &self.dma_apbperi_pms_monitor_violate_status_wr(),
            )
            .field(
                "dma_apbperi_pms_monitor_violate_status_byteen",
                &self.dma_apbperi_pms_monitor_violate_status_byteen(),
            )
            .finish()
    }
}
#[doc = "SENSITIVE_DMA_APBPERI_PMS_MONITOR_3_REG\n\nYou can [`read`](crate::Reg::read) this register and get [`dma_apbperi_pms_monitor_3::R`](R). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct DMA_APBPERI_PMS_MONITOR_3_SPEC;
impl crate::RegisterSpec for DMA_APBPERI_PMS_MONITOR_3_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`dma_apbperi_pms_monitor_3::R`](R) reader structure"]
impl crate::Readable for DMA_APBPERI_PMS_MONITOR_3_SPEC {}
#[doc = "`reset()` method sets DMA_APBPERI_PMS_MONITOR_3 to value 0"]
impl crate::Resettable for DMA_APBPERI_PMS_MONITOR_3_SPEC {}
