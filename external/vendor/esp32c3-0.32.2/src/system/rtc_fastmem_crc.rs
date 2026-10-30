#[doc = "Register `RTC_FASTMEM_CRC` reader"]
pub type R = crate::R<RTC_FASTMEM_CRC_SPEC>;
#[doc = "Field `RTC_MEM_CRC_RES` reader - reg_rtc_mem_crc_res"]
pub type RTC_MEM_CRC_RES_R = crate::FieldReader<u32>;
impl R {
    #[doc = "Bits 0:31 - reg_rtc_mem_crc_res"]
    #[inline(always)]
    pub fn rtc_mem_crc_res(&self) -> RTC_MEM_CRC_RES_R {
        RTC_MEM_CRC_RES_R::new(self.bits)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("RTC_FASTMEM_CRC")
            .field("rtc_mem_crc_res", &self.rtc_mem_crc_res())
            .finish()
    }
}
#[doc = "reserved\n\nYou can [`read`](crate::Reg::read) this register and get [`rtc_fastmem_crc::R`](R). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct RTC_FASTMEM_CRC_SPEC;
impl crate::RegisterSpec for RTC_FASTMEM_CRC_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`rtc_fastmem_crc::R`](R) reader structure"]
impl crate::Readable for RTC_FASTMEM_CRC_SPEC {}
#[doc = "`reset()` method sets RTC_FASTMEM_CRC to value 0"]
impl crate::Resettable for RTC_FASTMEM_CRC_SPEC {}
