#[doc = "Register `CTRL1` reader"]
pub type R = crate::R<CTRL1_SPEC>;
#[doc = "Register `CTRL1` writer"]
pub type W = crate::W<CTRL1_SPEC>;
#[doc = "Field `CLK_MODE` reader - SPI clock mode bits. 0: SPI clock is off when CS inactive 1: SPI clock is delayed one cycle after CS inactive 2: SPI clock is delayed two cycles after CS inactive 3: SPI clock is alwasy on."]
pub type CLK_MODE_R = crate::FieldReader;
#[doc = "Field `CLK_MODE` writer - SPI clock mode bits. 0: SPI clock is off when CS inactive 1: SPI clock is delayed one cycle after CS inactive 2: SPI clock is delayed two cycles after CS inactive 3: SPI clock is alwasy on."]
pub type CLK_MODE_W<'a, REG> = crate::FieldWriter<'a, REG, 2>;
#[doc = "Field `SPI_AR_SIZE0_1_SUPPORT_EN` reader - 1: MSPI supports ARSIZE 0~3. When ARSIZE =0~2, MSPI read address is 4*n and reply the real AXI read data back. 0: When ARSIZE 0~1, MSPI reply SLV_ERR."]
pub type SPI_AR_SIZE0_1_SUPPORT_EN_R = crate::BitReader;
#[doc = "Field `SPI_AR_SIZE0_1_SUPPORT_EN` writer - 1: MSPI supports ARSIZE 0~3. When ARSIZE =0~2, MSPI read address is 4*n and reply the real AXI read data back. 0: When ARSIZE 0~1, MSPI reply SLV_ERR."]
pub type SPI_AR_SIZE0_1_SUPPORT_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SPI_AW_SIZE0_1_SUPPORT_EN` reader - 1: MSPI supports AWSIZE 0~3. 0: When AWSIZE 0~1, MSPI reply SLV_ERR."]
pub type SPI_AW_SIZE0_1_SUPPORT_EN_R = crate::BitReader;
#[doc = "Field `SPI_AW_SIZE0_1_SUPPORT_EN` writer - 1: MSPI supports AWSIZE 0~3. 0: When AWSIZE 0~1, MSPI reply SLV_ERR."]
pub type SPI_AW_SIZE0_1_SUPPORT_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SPI_AXI_RDATA_BACK_FAST` reader - 1: Reply AXI read data to AXI bus when one AXI read beat data is available. 0: Reply AXI read data to AXI bus when all the read data is available."]
pub type SPI_AXI_RDATA_BACK_FAST_R = crate::BitReader;
#[doc = "Field `RRESP_ECC_ERR_EN` reader - 1: RRESP is SLV_ERR when there is a ECC error in AXI read data. 0: RRESP is OKAY when there is a ECC error in AXI read data. The ECC error information is recorded in SPI_MEM_ECC_ERR_ADDR_REG."]
pub type RRESP_ECC_ERR_EN_R = crate::BitReader;
#[doc = "Field `RRESP_ECC_ERR_EN` writer - 1: RRESP is SLV_ERR when there is a ECC error in AXI read data. 0: RRESP is OKAY when there is a ECC error in AXI read data. The ECC error information is recorded in SPI_MEM_ECC_ERR_ADDR_REG."]
pub type RRESP_ECC_ERR_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `AR_SPLICE_EN` reader - Set this bit to enable AXI Read Splice-transfer."]
pub type AR_SPLICE_EN_R = crate::BitReader;
#[doc = "Field `AW_SPLICE_EN` reader - Set this bit to enable AXI Write Splice-transfer."]
pub type AW_SPLICE_EN_R = crate::BitReader;
#[doc = "Field `RAM0_EN` reader - When SPI_MEM_DUAL_RAM_EN is 0 and SPI_MEM_RAM0_EN is 1, only EXT_RAM0 will be accessed. When SPI_MEM_DUAL_RAM_EN is 0 and SPI_MEM_RAM0_EN is 0, only EXT_RAM1 will be accessed. When SPI_MEM_DUAL_RAM_EN is 1, EXT_RAM0 and EXT_RAM1 will be accessed at the same time."]
pub type RAM0_EN_R = crate::BitReader;
#[doc = "Field `DUAL_RAM_EN` reader - Set this bit to enable DUAL-RAM mode, EXT_RAM0 and EXT_RAM1 will be accessed at the same time."]
pub type DUAL_RAM_EN_R = crate::BitReader;
#[doc = "Field `FAST_WRITE_EN` reader - Set this bit to write data faster, do not wait write data has been stored in tx_bus_fifo_l2. It will wait 4*T_clk_ctrl to insure the write data has been stored in tx_bus_fifo_l2."]
pub type FAST_WRITE_EN_R = crate::BitReader;
#[doc = "Field `FAST_WRITE_EN` writer - Set this bit to write data faster, do not wait write data has been stored in tx_bus_fifo_l2. It will wait 4*T_clk_ctrl to insure the write data has been stored in tx_bus_fifo_l2."]
pub type FAST_WRITE_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `RXFIFO_RST` writer - The synchronous reset signal for SPI0 RX AFIFO and all the AES_MSPI SYNC FIFO to receive signals from AXI. Set this bit to reset these FIFO."]
pub type RXFIFO_RST_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `TXFIFO_RST` writer - The synchronous reset signal for SPI0 TX AFIFO and all the AES_MSPI SYNC FIFO to send signals to AXI. Set this bit to reset these FIFO."]
pub type TXFIFO_RST_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bits 0:1 - SPI clock mode bits. 0: SPI clock is off when CS inactive 1: SPI clock is delayed one cycle after CS inactive 2: SPI clock is delayed two cycles after CS inactive 3: SPI clock is alwasy on."]
    #[inline(always)]
    pub fn clk_mode(&self) -> CLK_MODE_R {
        CLK_MODE_R::new((self.bits & 3) as u8)
    }
    #[doc = "Bit 21 - 1: MSPI supports ARSIZE 0~3. When ARSIZE =0~2, MSPI read address is 4*n and reply the real AXI read data back. 0: When ARSIZE 0~1, MSPI reply SLV_ERR."]
    #[inline(always)]
    pub fn spi_ar_size0_1_support_en(&self) -> SPI_AR_SIZE0_1_SUPPORT_EN_R {
        SPI_AR_SIZE0_1_SUPPORT_EN_R::new(((self.bits >> 21) & 1) != 0)
    }
    #[doc = "Bit 22 - 1: MSPI supports AWSIZE 0~3. 0: When AWSIZE 0~1, MSPI reply SLV_ERR."]
    #[inline(always)]
    pub fn spi_aw_size0_1_support_en(&self) -> SPI_AW_SIZE0_1_SUPPORT_EN_R {
        SPI_AW_SIZE0_1_SUPPORT_EN_R::new(((self.bits >> 22) & 1) != 0)
    }
    #[doc = "Bit 23 - 1: Reply AXI read data to AXI bus when one AXI read beat data is available. 0: Reply AXI read data to AXI bus when all the read data is available."]
    #[inline(always)]
    pub fn spi_axi_rdata_back_fast(&self) -> SPI_AXI_RDATA_BACK_FAST_R {
        SPI_AXI_RDATA_BACK_FAST_R::new(((self.bits >> 23) & 1) != 0)
    }
    #[doc = "Bit 24 - 1: RRESP is SLV_ERR when there is a ECC error in AXI read data. 0: RRESP is OKAY when there is a ECC error in AXI read data. The ECC error information is recorded in SPI_MEM_ECC_ERR_ADDR_REG."]
    #[inline(always)]
    pub fn rresp_ecc_err_en(&self) -> RRESP_ECC_ERR_EN_R {
        RRESP_ECC_ERR_EN_R::new(((self.bits >> 24) & 1) != 0)
    }
    #[doc = "Bit 25 - Set this bit to enable AXI Read Splice-transfer."]
    #[inline(always)]
    pub fn ar_splice_en(&self) -> AR_SPLICE_EN_R {
        AR_SPLICE_EN_R::new(((self.bits >> 25) & 1) != 0)
    }
    #[doc = "Bit 26 - Set this bit to enable AXI Write Splice-transfer."]
    #[inline(always)]
    pub fn aw_splice_en(&self) -> AW_SPLICE_EN_R {
        AW_SPLICE_EN_R::new(((self.bits >> 26) & 1) != 0)
    }
    #[doc = "Bit 27 - When SPI_MEM_DUAL_RAM_EN is 0 and SPI_MEM_RAM0_EN is 1, only EXT_RAM0 will be accessed. When SPI_MEM_DUAL_RAM_EN is 0 and SPI_MEM_RAM0_EN is 0, only EXT_RAM1 will be accessed. When SPI_MEM_DUAL_RAM_EN is 1, EXT_RAM0 and EXT_RAM1 will be accessed at the same time."]
    #[inline(always)]
    pub fn ram0_en(&self) -> RAM0_EN_R {
        RAM0_EN_R::new(((self.bits >> 27) & 1) != 0)
    }
    #[doc = "Bit 28 - Set this bit to enable DUAL-RAM mode, EXT_RAM0 and EXT_RAM1 will be accessed at the same time."]
    #[inline(always)]
    pub fn dual_ram_en(&self) -> DUAL_RAM_EN_R {
        DUAL_RAM_EN_R::new(((self.bits >> 28) & 1) != 0)
    }
    #[doc = "Bit 29 - Set this bit to write data faster, do not wait write data has been stored in tx_bus_fifo_l2. It will wait 4*T_clk_ctrl to insure the write data has been stored in tx_bus_fifo_l2."]
    #[inline(always)]
    pub fn fast_write_en(&self) -> FAST_WRITE_EN_R {
        FAST_WRITE_EN_R::new(((self.bits >> 29) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("CTRL1")
            .field("clk_mode", &self.clk_mode())
            .field(
                "spi_ar_size0_1_support_en",
                &self.spi_ar_size0_1_support_en(),
            )
            .field(
                "spi_aw_size0_1_support_en",
                &self.spi_aw_size0_1_support_en(),
            )
            .field("spi_axi_rdata_back_fast", &self.spi_axi_rdata_back_fast())
            .field("rresp_ecc_err_en", &self.rresp_ecc_err_en())
            .field("ar_splice_en", &self.ar_splice_en())
            .field("aw_splice_en", &self.aw_splice_en())
            .field("ram0_en", &self.ram0_en())
            .field("dual_ram_en", &self.dual_ram_en())
            .field("fast_write_en", &self.fast_write_en())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:1 - SPI clock mode bits. 0: SPI clock is off when CS inactive 1: SPI clock is delayed one cycle after CS inactive 2: SPI clock is delayed two cycles after CS inactive 3: SPI clock is alwasy on."]
    #[inline(always)]
    pub fn clk_mode(&mut self) -> CLK_MODE_W<'_, CTRL1_SPEC> {
        CLK_MODE_W::new(self, 0)
    }
    #[doc = "Bit 21 - 1: MSPI supports ARSIZE 0~3. When ARSIZE =0~2, MSPI read address is 4*n and reply the real AXI read data back. 0: When ARSIZE 0~1, MSPI reply SLV_ERR."]
    #[inline(always)]
    pub fn spi_ar_size0_1_support_en(&mut self) -> SPI_AR_SIZE0_1_SUPPORT_EN_W<'_, CTRL1_SPEC> {
        SPI_AR_SIZE0_1_SUPPORT_EN_W::new(self, 21)
    }
    #[doc = "Bit 22 - 1: MSPI supports AWSIZE 0~3. 0: When AWSIZE 0~1, MSPI reply SLV_ERR."]
    #[inline(always)]
    pub fn spi_aw_size0_1_support_en(&mut self) -> SPI_AW_SIZE0_1_SUPPORT_EN_W<'_, CTRL1_SPEC> {
        SPI_AW_SIZE0_1_SUPPORT_EN_W::new(self, 22)
    }
    #[doc = "Bit 24 - 1: RRESP is SLV_ERR when there is a ECC error in AXI read data. 0: RRESP is OKAY when there is a ECC error in AXI read data. The ECC error information is recorded in SPI_MEM_ECC_ERR_ADDR_REG."]
    #[inline(always)]
    pub fn rresp_ecc_err_en(&mut self) -> RRESP_ECC_ERR_EN_W<'_, CTRL1_SPEC> {
        RRESP_ECC_ERR_EN_W::new(self, 24)
    }
    #[doc = "Bit 29 - Set this bit to write data faster, do not wait write data has been stored in tx_bus_fifo_l2. It will wait 4*T_clk_ctrl to insure the write data has been stored in tx_bus_fifo_l2."]
    #[inline(always)]
    pub fn fast_write_en(&mut self) -> FAST_WRITE_EN_W<'_, CTRL1_SPEC> {
        FAST_WRITE_EN_W::new(self, 29)
    }
    #[doc = "Bit 30 - The synchronous reset signal for SPI0 RX AFIFO and all the AES_MSPI SYNC FIFO to receive signals from AXI. Set this bit to reset these FIFO."]
    #[inline(always)]
    pub fn rxfifo_rst(&mut self) -> RXFIFO_RST_W<'_, CTRL1_SPEC> {
        RXFIFO_RST_W::new(self, 30)
    }
    #[doc = "Bit 31 - The synchronous reset signal for SPI0 TX AFIFO and all the AES_MSPI SYNC FIFO to send signals to AXI. Set this bit to reset these FIFO."]
    #[inline(always)]
    pub fn txfifo_rst(&mut self) -> TXFIFO_RST_W<'_, CTRL1_SPEC> {
        TXFIFO_RST_W::new(self, 31)
    }
}
#[doc = "SPI0 control1 register.\n\nYou can [`read`](crate::Reg::read) this register and get [`ctrl1::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`ctrl1::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct CTRL1_SPEC;
impl crate::RegisterSpec for CTRL1_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`ctrl1::R`](R) reader structure"]
impl crate::Readable for CTRL1_SPEC {}
#[doc = "`write(|w| ..)` method takes [`ctrl1::W`](W) writer structure"]
impl crate::Writable for CTRL1_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets CTRL1 to value 0x28e0_0000"]
impl crate::Resettable for CTRL1_SPEC {
    const RESET_VALUE: u32 = 0x28e0_0000;
}
