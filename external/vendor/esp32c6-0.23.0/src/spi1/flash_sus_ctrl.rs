#[doc = "Register `FLASH_SUS_CTRL` reader"]
pub type R = crate::R<FLASH_SUS_CTRL_SPEC>;
#[doc = "Register `FLASH_SUS_CTRL` writer"]
pub type W = crate::W<FLASH_SUS_CTRL_SPEC>;
#[doc = "Field `FLASH_PER` reader - program erase resume bit, program erase suspend operation will be triggered when the bit is set. The bit will be cleared once the operation done.1: enable 0: disable."]
pub type FLASH_PER_R = crate::BitReader;
#[doc = "Field `FLASH_PER` writer - program erase resume bit, program erase suspend operation will be triggered when the bit is set. The bit will be cleared once the operation done.1: enable 0: disable."]
pub type FLASH_PER_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `FLASH_PES` reader - program erase suspend bit, program erase suspend operation will be triggered when the bit is set. The bit will be cleared once the operation done.1: enable 0: disable."]
pub type FLASH_PES_R = crate::BitReader;
#[doc = "Field `FLASH_PES` writer - program erase suspend bit, program erase suspend operation will be triggered when the bit is set. The bit will be cleared once the operation done.1: enable 0: disable."]
pub type FLASH_PES_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `FLASH_PER_WAIT_EN` reader - 1: SPI1 waits (SPI_MEM_CS_HOLD_DELAY_RES\\[9:0\\] * 4 or *128) SPI_CLK cycles after program erase resume command is sent. 0: SPI1 does not wait after program erase resume command is sent."]
pub type FLASH_PER_WAIT_EN_R = crate::BitReader;
#[doc = "Field `FLASH_PER_WAIT_EN` writer - 1: SPI1 waits (SPI_MEM_CS_HOLD_DELAY_RES\\[9:0\\] * 4 or *128) SPI_CLK cycles after program erase resume command is sent. 0: SPI1 does not wait after program erase resume command is sent."]
pub type FLASH_PER_WAIT_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `FLASH_PES_WAIT_EN` reader - 1: SPI1 waits (SPI_MEM_CS_HOLD_DELAY_RES\\[9:0\\] * 4 or *128) SPI_CLK cycles after program erase suspend command is sent. 0: SPI1 does not wait after program erase suspend command is sent."]
pub type FLASH_PES_WAIT_EN_R = crate::BitReader;
#[doc = "Field `FLASH_PES_WAIT_EN` writer - 1: SPI1 waits (SPI_MEM_CS_HOLD_DELAY_RES\\[9:0\\] * 4 or *128) SPI_CLK cycles after program erase suspend command is sent. 0: SPI1 does not wait after program erase suspend command is sent."]
pub type FLASH_PES_WAIT_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `PES_PER_EN` reader - Set this bit to enable PES end triggers PER transfer option. If this bit is 0, application should send PER after PES is done."]
pub type PES_PER_EN_R = crate::BitReader;
#[doc = "Field `PES_PER_EN` writer - Set this bit to enable PES end triggers PER transfer option. If this bit is 0, application should send PER after PES is done."]
pub type PES_PER_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `FLASH_PES_EN` reader - Set this bit to enable Auto-suspending function."]
pub type FLASH_PES_EN_R = crate::BitReader;
#[doc = "Field `FLASH_PES_EN` writer - Set this bit to enable Auto-suspending function."]
pub type FLASH_PES_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `PESR_END_MSK` reader - The mask value when check SUS/SUS1/SUS2 status bit. If the read status value is status_in\\[15:0\\](only status_in\\[7:0\\] is valid when only one byte of data is read out, status_in\\[15:0\\] is valid when two bytes of data are read out), SUS/SUS1/SUS2 = status_in\\[15:0\\]^ SPI_MEM_PESR_END_MSK\\[15:0\\]."]
pub type PESR_END_MSK_R = crate::FieldReader<u16>;
#[doc = "Field `PESR_END_MSK` writer - The mask value when check SUS/SUS1/SUS2 status bit. If the read status value is status_in\\[15:0\\](only status_in\\[7:0\\] is valid when only one byte of data is read out, status_in\\[15:0\\] is valid when two bytes of data are read out), SUS/SUS1/SUS2 = status_in\\[15:0\\]^ SPI_MEM_PESR_END_MSK\\[15:0\\]."]
pub type PESR_END_MSK_W<'a, REG> = crate::FieldWriter<'a, REG, 16, u16>;
#[doc = "Field `SPI_FMEM_RD_SUS_2B` reader - 1: Read two bytes when check flash SUS/SUS1/SUS2 status bit. 0: Read one byte when check flash SUS/SUS1/SUS2 status bit"]
pub type SPI_FMEM_RD_SUS_2B_R = crate::BitReader;
#[doc = "Field `SPI_FMEM_RD_SUS_2B` writer - 1: Read two bytes when check flash SUS/SUS1/SUS2 status bit. 0: Read one byte when check flash SUS/SUS1/SUS2 status bit"]
pub type SPI_FMEM_RD_SUS_2B_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `PER_END_EN` reader - 1: Both WIP and SUS/SUS1/SUS2 bits should be checked to insure the resume status of flash. 0: Only need to check WIP is 0."]
pub type PER_END_EN_R = crate::BitReader;
#[doc = "Field `PER_END_EN` writer - 1: Both WIP and SUS/SUS1/SUS2 bits should be checked to insure the resume status of flash. 0: Only need to check WIP is 0."]
pub type PER_END_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `PES_END_EN` reader - 1: Both WIP and SUS/SUS1/SUS2 bits should be checked to insure the suspend status of flash. 0: Only need to check WIP is 0."]
pub type PES_END_EN_R = crate::BitReader;
#[doc = "Field `PES_END_EN` writer - 1: Both WIP and SUS/SUS1/SUS2 bits should be checked to insure the suspend status of flash. 0: Only need to check WIP is 0."]
pub type PES_END_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SUS_TIMEOUT_CNT` reader - When SPI1 checks SUS/SUS1/SUS2 bits fail for SPI_MEM_SUS_TIMEOUT_CNT\\[6:0\\] times, it will be treated as check pass."]
pub type SUS_TIMEOUT_CNT_R = crate::FieldReader;
#[doc = "Field `SUS_TIMEOUT_CNT` writer - When SPI1 checks SUS/SUS1/SUS2 bits fail for SPI_MEM_SUS_TIMEOUT_CNT\\[6:0\\] times, it will be treated as check pass."]
pub type SUS_TIMEOUT_CNT_W<'a, REG> = crate::FieldWriter<'a, REG, 7>;
impl R {
    #[doc = "Bit 0 - program erase resume bit, program erase suspend operation will be triggered when the bit is set. The bit will be cleared once the operation done.1: enable 0: disable."]
    #[inline(always)]
    pub fn flash_per(&self) -> FLASH_PER_R {
        FLASH_PER_R::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - program erase suspend bit, program erase suspend operation will be triggered when the bit is set. The bit will be cleared once the operation done.1: enable 0: disable."]
    #[inline(always)]
    pub fn flash_pes(&self) -> FLASH_PES_R {
        FLASH_PES_R::new(((self.bits >> 1) & 1) != 0)
    }
    #[doc = "Bit 2 - 1: SPI1 waits (SPI_MEM_CS_HOLD_DELAY_RES\\[9:0\\] * 4 or *128) SPI_CLK cycles after program erase resume command is sent. 0: SPI1 does not wait after program erase resume command is sent."]
    #[inline(always)]
    pub fn flash_per_wait_en(&self) -> FLASH_PER_WAIT_EN_R {
        FLASH_PER_WAIT_EN_R::new(((self.bits >> 2) & 1) != 0)
    }
    #[doc = "Bit 3 - 1: SPI1 waits (SPI_MEM_CS_HOLD_DELAY_RES\\[9:0\\] * 4 or *128) SPI_CLK cycles after program erase suspend command is sent. 0: SPI1 does not wait after program erase suspend command is sent."]
    #[inline(always)]
    pub fn flash_pes_wait_en(&self) -> FLASH_PES_WAIT_EN_R {
        FLASH_PES_WAIT_EN_R::new(((self.bits >> 3) & 1) != 0)
    }
    #[doc = "Bit 4 - Set this bit to enable PES end triggers PER transfer option. If this bit is 0, application should send PER after PES is done."]
    #[inline(always)]
    pub fn pes_per_en(&self) -> PES_PER_EN_R {
        PES_PER_EN_R::new(((self.bits >> 4) & 1) != 0)
    }
    #[doc = "Bit 5 - Set this bit to enable Auto-suspending function."]
    #[inline(always)]
    pub fn flash_pes_en(&self) -> FLASH_PES_EN_R {
        FLASH_PES_EN_R::new(((self.bits >> 5) & 1) != 0)
    }
    #[doc = "Bits 6:21 - The mask value when check SUS/SUS1/SUS2 status bit. If the read status value is status_in\\[15:0\\](only status_in\\[7:0\\] is valid when only one byte of data is read out, status_in\\[15:0\\] is valid when two bytes of data are read out), SUS/SUS1/SUS2 = status_in\\[15:0\\]^ SPI_MEM_PESR_END_MSK\\[15:0\\]."]
    #[inline(always)]
    pub fn pesr_end_msk(&self) -> PESR_END_MSK_R {
        PESR_END_MSK_R::new(((self.bits >> 6) & 0xffff) as u16)
    }
    #[doc = "Bit 22 - 1: Read two bytes when check flash SUS/SUS1/SUS2 status bit. 0: Read one byte when check flash SUS/SUS1/SUS2 status bit"]
    #[inline(always)]
    pub fn spi_fmem_rd_sus_2b(&self) -> SPI_FMEM_RD_SUS_2B_R {
        SPI_FMEM_RD_SUS_2B_R::new(((self.bits >> 22) & 1) != 0)
    }
    #[doc = "Bit 23 - 1: Both WIP and SUS/SUS1/SUS2 bits should be checked to insure the resume status of flash. 0: Only need to check WIP is 0."]
    #[inline(always)]
    pub fn per_end_en(&self) -> PER_END_EN_R {
        PER_END_EN_R::new(((self.bits >> 23) & 1) != 0)
    }
    #[doc = "Bit 24 - 1: Both WIP and SUS/SUS1/SUS2 bits should be checked to insure the suspend status of flash. 0: Only need to check WIP is 0."]
    #[inline(always)]
    pub fn pes_end_en(&self) -> PES_END_EN_R {
        PES_END_EN_R::new(((self.bits >> 24) & 1) != 0)
    }
    #[doc = "Bits 25:31 - When SPI1 checks SUS/SUS1/SUS2 bits fail for SPI_MEM_SUS_TIMEOUT_CNT\\[6:0\\] times, it will be treated as check pass."]
    #[inline(always)]
    pub fn sus_timeout_cnt(&self) -> SUS_TIMEOUT_CNT_R {
        SUS_TIMEOUT_CNT_R::new(((self.bits >> 25) & 0x7f) as u8)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("FLASH_SUS_CTRL")
            .field("flash_per", &self.flash_per())
            .field("flash_pes", &self.flash_pes())
            .field("flash_per_wait_en", &self.flash_per_wait_en())
            .field("flash_pes_wait_en", &self.flash_pes_wait_en())
            .field("pes_per_en", &self.pes_per_en())
            .field("flash_pes_en", &self.flash_pes_en())
            .field("pesr_end_msk", &self.pesr_end_msk())
            .field("spi_fmem_rd_sus_2b", &self.spi_fmem_rd_sus_2b())
            .field("per_end_en", &self.per_end_en())
            .field("pes_end_en", &self.pes_end_en())
            .field("sus_timeout_cnt", &self.sus_timeout_cnt())
            .finish()
    }
}
impl W {
    #[doc = "Bit 0 - program erase resume bit, program erase suspend operation will be triggered when the bit is set. The bit will be cleared once the operation done.1: enable 0: disable."]
    #[inline(always)]
    pub fn flash_per(&mut self) -> FLASH_PER_W<'_, FLASH_SUS_CTRL_SPEC> {
        FLASH_PER_W::new(self, 0)
    }
    #[doc = "Bit 1 - program erase suspend bit, program erase suspend operation will be triggered when the bit is set. The bit will be cleared once the operation done.1: enable 0: disable."]
    #[inline(always)]
    pub fn flash_pes(&mut self) -> FLASH_PES_W<'_, FLASH_SUS_CTRL_SPEC> {
        FLASH_PES_W::new(self, 1)
    }
    #[doc = "Bit 2 - 1: SPI1 waits (SPI_MEM_CS_HOLD_DELAY_RES\\[9:0\\] * 4 or *128) SPI_CLK cycles after program erase resume command is sent. 0: SPI1 does not wait after program erase resume command is sent."]
    #[inline(always)]
    pub fn flash_per_wait_en(&mut self) -> FLASH_PER_WAIT_EN_W<'_, FLASH_SUS_CTRL_SPEC> {
        FLASH_PER_WAIT_EN_W::new(self, 2)
    }
    #[doc = "Bit 3 - 1: SPI1 waits (SPI_MEM_CS_HOLD_DELAY_RES\\[9:0\\] * 4 or *128) SPI_CLK cycles after program erase suspend command is sent. 0: SPI1 does not wait after program erase suspend command is sent."]
    #[inline(always)]
    pub fn flash_pes_wait_en(&mut self) -> FLASH_PES_WAIT_EN_W<'_, FLASH_SUS_CTRL_SPEC> {
        FLASH_PES_WAIT_EN_W::new(self, 3)
    }
    #[doc = "Bit 4 - Set this bit to enable PES end triggers PER transfer option. If this bit is 0, application should send PER after PES is done."]
    #[inline(always)]
    pub fn pes_per_en(&mut self) -> PES_PER_EN_W<'_, FLASH_SUS_CTRL_SPEC> {
        PES_PER_EN_W::new(self, 4)
    }
    #[doc = "Bit 5 - Set this bit to enable Auto-suspending function."]
    #[inline(always)]
    pub fn flash_pes_en(&mut self) -> FLASH_PES_EN_W<'_, FLASH_SUS_CTRL_SPEC> {
        FLASH_PES_EN_W::new(self, 5)
    }
    #[doc = "Bits 6:21 - The mask value when check SUS/SUS1/SUS2 status bit. If the read status value is status_in\\[15:0\\](only status_in\\[7:0\\] is valid when only one byte of data is read out, status_in\\[15:0\\] is valid when two bytes of data are read out), SUS/SUS1/SUS2 = status_in\\[15:0\\]^ SPI_MEM_PESR_END_MSK\\[15:0\\]."]
    #[inline(always)]
    pub fn pesr_end_msk(&mut self) -> PESR_END_MSK_W<'_, FLASH_SUS_CTRL_SPEC> {
        PESR_END_MSK_W::new(self, 6)
    }
    #[doc = "Bit 22 - 1: Read two bytes when check flash SUS/SUS1/SUS2 status bit. 0: Read one byte when check flash SUS/SUS1/SUS2 status bit"]
    #[inline(always)]
    pub fn spi_fmem_rd_sus_2b(&mut self) -> SPI_FMEM_RD_SUS_2B_W<'_, FLASH_SUS_CTRL_SPEC> {
        SPI_FMEM_RD_SUS_2B_W::new(self, 22)
    }
    #[doc = "Bit 23 - 1: Both WIP and SUS/SUS1/SUS2 bits should be checked to insure the resume status of flash. 0: Only need to check WIP is 0."]
    #[inline(always)]
    pub fn per_end_en(&mut self) -> PER_END_EN_W<'_, FLASH_SUS_CTRL_SPEC> {
        PER_END_EN_W::new(self, 23)
    }
    #[doc = "Bit 24 - 1: Both WIP and SUS/SUS1/SUS2 bits should be checked to insure the suspend status of flash. 0: Only need to check WIP is 0."]
    #[inline(always)]
    pub fn pes_end_en(&mut self) -> PES_END_EN_W<'_, FLASH_SUS_CTRL_SPEC> {
        PES_END_EN_W::new(self, 24)
    }
    #[doc = "Bits 25:31 - When SPI1 checks SUS/SUS1/SUS2 bits fail for SPI_MEM_SUS_TIMEOUT_CNT\\[6:0\\] times, it will be treated as check pass."]
    #[inline(always)]
    pub fn sus_timeout_cnt(&mut self) -> SUS_TIMEOUT_CNT_W<'_, FLASH_SUS_CTRL_SPEC> {
        SUS_TIMEOUT_CNT_W::new(self, 25)
    }
}
#[doc = "SPI1 flash suspend control register\n\nYou can [`read`](crate::Reg::read) this register and get [`flash_sus_ctrl::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`flash_sus_ctrl::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct FLASH_SUS_CTRL_SPEC;
impl crate::RegisterSpec for FLASH_SUS_CTRL_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`flash_sus_ctrl::R`](R) reader structure"]
impl crate::Readable for FLASH_SUS_CTRL_SPEC {}
#[doc = "`write(|w| ..)` method takes [`flash_sus_ctrl::W`](W) writer structure"]
impl crate::Writable for FLASH_SUS_CTRL_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets FLASH_SUS_CTRL to value 0x0800_2000"]
impl crate::Resettable for FLASH_SUS_CTRL_SPEC {
    const RESET_VALUE: u32 = 0x0800_2000;
}
