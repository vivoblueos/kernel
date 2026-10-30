#[doc = "Register `RTC_FASTMEM_CONFIG` reader"]
pub type R = crate::R<RTC_FASTMEM_CONFIG_SPEC>;
#[doc = "Register `RTC_FASTMEM_CONFIG` writer"]
pub type W = crate::W<RTC_FASTMEM_CONFIG_SPEC>;
#[doc = "Field `RTC_MEM_CRC_START` reader - reg_rtc_mem_crc_start"]
pub type RTC_MEM_CRC_START_R = crate::BitReader;
#[doc = "Field `RTC_MEM_CRC_START` writer - reg_rtc_mem_crc_start"]
pub type RTC_MEM_CRC_START_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `RTC_MEM_CRC_ADDR` reader - reg_rtc_mem_crc_addr"]
pub type RTC_MEM_CRC_ADDR_R = crate::FieldReader<u16>;
#[doc = "Field `RTC_MEM_CRC_ADDR` writer - reg_rtc_mem_crc_addr"]
pub type RTC_MEM_CRC_ADDR_W<'a, REG> = crate::FieldWriter<'a, REG, 11, u16>;
#[doc = "Field `RTC_MEM_CRC_LEN` reader - reg_rtc_mem_crc_len"]
pub type RTC_MEM_CRC_LEN_R = crate::FieldReader<u16>;
#[doc = "Field `RTC_MEM_CRC_LEN` writer - reg_rtc_mem_crc_len"]
pub type RTC_MEM_CRC_LEN_W<'a, REG> = crate::FieldWriter<'a, REG, 11, u16>;
#[doc = "Field `RTC_MEM_CRC_FINISH` reader - reg_rtc_mem_crc_finish"]
pub type RTC_MEM_CRC_FINISH_R = crate::BitReader;
impl R {
    #[doc = "Bit 8 - reg_rtc_mem_crc_start"]
    #[inline(always)]
    pub fn rtc_mem_crc_start(&self) -> RTC_MEM_CRC_START_R {
        RTC_MEM_CRC_START_R::new(((self.bits >> 8) & 1) != 0)
    }
    #[doc = "Bits 9:19 - reg_rtc_mem_crc_addr"]
    #[inline(always)]
    pub fn rtc_mem_crc_addr(&self) -> RTC_MEM_CRC_ADDR_R {
        RTC_MEM_CRC_ADDR_R::new(((self.bits >> 9) & 0x07ff) as u16)
    }
    #[doc = "Bits 20:30 - reg_rtc_mem_crc_len"]
    #[inline(always)]
    pub fn rtc_mem_crc_len(&self) -> RTC_MEM_CRC_LEN_R {
        RTC_MEM_CRC_LEN_R::new(((self.bits >> 20) & 0x07ff) as u16)
    }
    #[doc = "Bit 31 - reg_rtc_mem_crc_finish"]
    #[inline(always)]
    pub fn rtc_mem_crc_finish(&self) -> RTC_MEM_CRC_FINISH_R {
        RTC_MEM_CRC_FINISH_R::new(((self.bits >> 31) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("RTC_FASTMEM_CONFIG")
            .field("rtc_mem_crc_start", &self.rtc_mem_crc_start())
            .field("rtc_mem_crc_addr", &self.rtc_mem_crc_addr())
            .field("rtc_mem_crc_len", &self.rtc_mem_crc_len())
            .field("rtc_mem_crc_finish", &self.rtc_mem_crc_finish())
            .finish()
    }
}
impl W {
    #[doc = "Bit 8 - reg_rtc_mem_crc_start"]
    #[inline(always)]
    pub fn rtc_mem_crc_start(&mut self) -> RTC_MEM_CRC_START_W<'_, RTC_FASTMEM_CONFIG_SPEC> {
        RTC_MEM_CRC_START_W::new(self, 8)
    }
    #[doc = "Bits 9:19 - reg_rtc_mem_crc_addr"]
    #[inline(always)]
    pub fn rtc_mem_crc_addr(&mut self) -> RTC_MEM_CRC_ADDR_W<'_, RTC_FASTMEM_CONFIG_SPEC> {
        RTC_MEM_CRC_ADDR_W::new(self, 9)
    }
    #[doc = "Bits 20:30 - reg_rtc_mem_crc_len"]
    #[inline(always)]
    pub fn rtc_mem_crc_len(&mut self) -> RTC_MEM_CRC_LEN_W<'_, RTC_FASTMEM_CONFIG_SPEC> {
        RTC_MEM_CRC_LEN_W::new(self, 20)
    }
}
#[doc = "fast memory config register\n\nYou can [`read`](crate::Reg::read) this register and get [`rtc_fastmem_config::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`rtc_fastmem_config::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct RTC_FASTMEM_CONFIG_SPEC;
impl crate::RegisterSpec for RTC_FASTMEM_CONFIG_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`rtc_fastmem_config::R`](R) reader structure"]
impl crate::Readable for RTC_FASTMEM_CONFIG_SPEC {}
#[doc = "`write(|w| ..)` method takes [`rtc_fastmem_config::W`](W) writer structure"]
impl crate::Writable for RTC_FASTMEM_CONFIG_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets RTC_FASTMEM_CONFIG to value 0x7ff0_0000"]
impl crate::Resettable for RTC_FASTMEM_CONFIG_SPEC {
    const RESET_VALUE: u32 = 0x7ff0_0000;
}
