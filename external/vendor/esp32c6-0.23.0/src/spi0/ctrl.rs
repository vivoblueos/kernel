#[doc = "Register `CTRL` reader"]
pub type R = crate::R<CTRL_SPEC>;
#[doc = "Register `CTRL` writer"]
pub type W = crate::W<CTRL_SPEC>;
#[doc = "Field `WDUMMY_DQS_ALWAYS_OUT` reader - In the dummy phase of an MSPI write data transfer when accesses to flash, the level of SPI_DQS is output by the MSPI controller."]
pub type WDUMMY_DQS_ALWAYS_OUT_R = crate::BitReader;
#[doc = "Field `WDUMMY_ALWAYS_OUT` reader - In the dummy phase of an MSPI write data transfer when accesses to flash, the level of SPI_IO\\[7:0\\] is output by the MSPI controller."]
pub type WDUMMY_ALWAYS_OUT_R = crate::BitReader;
#[doc = "Field `WDUMMY_ALWAYS_OUT` writer - In the dummy phase of an MSPI write data transfer when accesses to flash, the level of SPI_IO\\[7:0\\] is output by the MSPI controller."]
pub type WDUMMY_ALWAYS_OUT_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `FDUMMY_RIN` reader - In an MSPI read data transfer when accesses to flash, the level of SPI_IO\\[7:0\\] is output by the MSPI controller in the first half part of dummy phase. It is used to mask invalid SPI_DQS in the half part of dummy phase."]
pub type FDUMMY_RIN_R = crate::BitReader;
#[doc = "Field `FDUMMY_RIN` writer - In an MSPI read data transfer when accesses to flash, the level of SPI_IO\\[7:0\\] is output by the MSPI controller in the first half part of dummy phase. It is used to mask invalid SPI_DQS in the half part of dummy phase."]
pub type FDUMMY_RIN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `FDUMMY_WOUT` reader - In an MSPI write data transfer when accesses to flash, the level of SPI_IO\\[7:0\\] is output by the MSPI controller in the second half part of dummy phase. It is used to pre-drive flash."]
pub type FDUMMY_WOUT_R = crate::BitReader;
#[doc = "Field `FDUMMY_WOUT` writer - In an MSPI write data transfer when accesses to flash, the level of SPI_IO\\[7:0\\] is output by the MSPI controller in the second half part of dummy phase. It is used to pre-drive flash."]
pub type FDUMMY_WOUT_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `FDOUT_OCT` reader - Apply 8 signals during write-data phase 1:enable 0: disable"]
pub type FDOUT_OCT_R = crate::BitReader;
#[doc = "Field `FDIN_OCT` reader - Apply 8 signals during read-data phase 1:enable 0: disable"]
pub type FDIN_OCT_R = crate::BitReader;
#[doc = "Field `FADDR_OCT` reader - Apply 8 signals during address phase 1:enable 0: disable"]
pub type FADDR_OCT_R = crate::BitReader;
#[doc = "Field `FCMD_QUAD` reader - Apply 4 signals during command phase 1:enable 0: disable"]
pub type FCMD_QUAD_R = crate::BitReader;
#[doc = "Field `FCMD_QUAD` writer - Apply 4 signals during command phase 1:enable 0: disable"]
pub type FCMD_QUAD_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `FCMD_OCT` reader - Apply 8 signals during command phase 1:enable 0: disable"]
pub type FCMD_OCT_R = crate::BitReader;
#[doc = "Field `FASTRD_MODE` reader - This bit enable the bits: SPI_MEM_FREAD_QIO, SPI_MEM_FREAD_DIO, SPI_MEM_FREAD_QOUT and SPI_MEM_FREAD_DOUT. 1: enable 0: disable."]
pub type FASTRD_MODE_R = crate::BitReader;
#[doc = "Field `FASTRD_MODE` writer - This bit enable the bits: SPI_MEM_FREAD_QIO, SPI_MEM_FREAD_DIO, SPI_MEM_FREAD_QOUT and SPI_MEM_FREAD_DOUT. 1: enable 0: disable."]
pub type FASTRD_MODE_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `FREAD_DUAL` reader - In the read operations, read-data phase apply 2 signals. 1: enable 0: disable."]
pub type FREAD_DUAL_R = crate::BitReader;
#[doc = "Field `FREAD_DUAL` writer - In the read operations, read-data phase apply 2 signals. 1: enable 0: disable."]
pub type FREAD_DUAL_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `Q_POL` reader - The bit is used to set MISO line polarity, 1: high 0, low"]
pub type Q_POL_R = crate::BitReader;
#[doc = "Field `Q_POL` writer - The bit is used to set MISO line polarity, 1: high 0, low"]
pub type Q_POL_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `D_POL` reader - The bit is used to set MOSI line polarity, 1: high 0, low"]
pub type D_POL_R = crate::BitReader;
#[doc = "Field `D_POL` writer - The bit is used to set MOSI line polarity, 1: high 0, low"]
pub type D_POL_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `FREAD_QUAD` reader - In the read operations read-data phase apply 4 signals. 1: enable 0: disable."]
pub type FREAD_QUAD_R = crate::BitReader;
#[doc = "Field `FREAD_QUAD` writer - In the read operations read-data phase apply 4 signals. 1: enable 0: disable."]
pub type FREAD_QUAD_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `WP` reader - Write protect signal output when SPI is idle. 1: output high, 0: output low."]
pub type WP_R = crate::BitReader;
#[doc = "Field `WP` writer - Write protect signal output when SPI is idle. 1: output high, 0: output low."]
pub type WP_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `FREAD_DIO` reader - In the read operations address phase and read-data phase apply 2 signals. 1: enable 0: disable."]
pub type FREAD_DIO_R = crate::BitReader;
#[doc = "Field `FREAD_DIO` writer - In the read operations address phase and read-data phase apply 2 signals. 1: enable 0: disable."]
pub type FREAD_DIO_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `FREAD_QIO` reader - In the read operations address phase and read-data phase apply 4 signals. 1: enable 0: disable."]
pub type FREAD_QIO_R = crate::BitReader;
#[doc = "Field `FREAD_QIO` writer - In the read operations address phase and read-data phase apply 4 signals. 1: enable 0: disable."]
pub type FREAD_QIO_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `DQS_IE_ALWAYS_ON` reader - When accesses to flash, 1: the IE signals of pads connected to SPI_DQS are always 1. 0: Others."]
pub type DQS_IE_ALWAYS_ON_R = crate::BitReader;
#[doc = "Field `DATA_IE_ALWAYS_ON` reader - When accesses to flash, 1: the IE signals of pads connected to SPI_IO\\[7:0\\] are always 1. 0: Others."]
pub type DATA_IE_ALWAYS_ON_R = crate::BitReader;
#[doc = "Field `DATA_IE_ALWAYS_ON` writer - When accesses to flash, 1: the IE signals of pads connected to SPI_IO\\[7:0\\] are always 1. 0: Others."]
pub type DATA_IE_ALWAYS_ON_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 0 - In the dummy phase of an MSPI write data transfer when accesses to flash, the level of SPI_DQS is output by the MSPI controller."]
    #[inline(always)]
    pub fn wdummy_dqs_always_out(&self) -> WDUMMY_DQS_ALWAYS_OUT_R {
        WDUMMY_DQS_ALWAYS_OUT_R::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - In the dummy phase of an MSPI write data transfer when accesses to flash, the level of SPI_IO\\[7:0\\] is output by the MSPI controller."]
    #[inline(always)]
    pub fn wdummy_always_out(&self) -> WDUMMY_ALWAYS_OUT_R {
        WDUMMY_ALWAYS_OUT_R::new(((self.bits >> 1) & 1) != 0)
    }
    #[doc = "Bit 2 - In an MSPI read data transfer when accesses to flash, the level of SPI_IO\\[7:0\\] is output by the MSPI controller in the first half part of dummy phase. It is used to mask invalid SPI_DQS in the half part of dummy phase."]
    #[inline(always)]
    pub fn fdummy_rin(&self) -> FDUMMY_RIN_R {
        FDUMMY_RIN_R::new(((self.bits >> 2) & 1) != 0)
    }
    #[doc = "Bit 3 - In an MSPI write data transfer when accesses to flash, the level of SPI_IO\\[7:0\\] is output by the MSPI controller in the second half part of dummy phase. It is used to pre-drive flash."]
    #[inline(always)]
    pub fn fdummy_wout(&self) -> FDUMMY_WOUT_R {
        FDUMMY_WOUT_R::new(((self.bits >> 3) & 1) != 0)
    }
    #[doc = "Bit 4 - Apply 8 signals during write-data phase 1:enable 0: disable"]
    #[inline(always)]
    pub fn fdout_oct(&self) -> FDOUT_OCT_R {
        FDOUT_OCT_R::new(((self.bits >> 4) & 1) != 0)
    }
    #[doc = "Bit 5 - Apply 8 signals during read-data phase 1:enable 0: disable"]
    #[inline(always)]
    pub fn fdin_oct(&self) -> FDIN_OCT_R {
        FDIN_OCT_R::new(((self.bits >> 5) & 1) != 0)
    }
    #[doc = "Bit 6 - Apply 8 signals during address phase 1:enable 0: disable"]
    #[inline(always)]
    pub fn faddr_oct(&self) -> FADDR_OCT_R {
        FADDR_OCT_R::new(((self.bits >> 6) & 1) != 0)
    }
    #[doc = "Bit 8 - Apply 4 signals during command phase 1:enable 0: disable"]
    #[inline(always)]
    pub fn fcmd_quad(&self) -> FCMD_QUAD_R {
        FCMD_QUAD_R::new(((self.bits >> 8) & 1) != 0)
    }
    #[doc = "Bit 9 - Apply 8 signals during command phase 1:enable 0: disable"]
    #[inline(always)]
    pub fn fcmd_oct(&self) -> FCMD_OCT_R {
        FCMD_OCT_R::new(((self.bits >> 9) & 1) != 0)
    }
    #[doc = "Bit 13 - This bit enable the bits: SPI_MEM_FREAD_QIO, SPI_MEM_FREAD_DIO, SPI_MEM_FREAD_QOUT and SPI_MEM_FREAD_DOUT. 1: enable 0: disable."]
    #[inline(always)]
    pub fn fastrd_mode(&self) -> FASTRD_MODE_R {
        FASTRD_MODE_R::new(((self.bits >> 13) & 1) != 0)
    }
    #[doc = "Bit 14 - In the read operations, read-data phase apply 2 signals. 1: enable 0: disable."]
    #[inline(always)]
    pub fn fread_dual(&self) -> FREAD_DUAL_R {
        FREAD_DUAL_R::new(((self.bits >> 14) & 1) != 0)
    }
    #[doc = "Bit 18 - The bit is used to set MISO line polarity, 1: high 0, low"]
    #[inline(always)]
    pub fn q_pol(&self) -> Q_POL_R {
        Q_POL_R::new(((self.bits >> 18) & 1) != 0)
    }
    #[doc = "Bit 19 - The bit is used to set MOSI line polarity, 1: high 0, low"]
    #[inline(always)]
    pub fn d_pol(&self) -> D_POL_R {
        D_POL_R::new(((self.bits >> 19) & 1) != 0)
    }
    #[doc = "Bit 20 - In the read operations read-data phase apply 4 signals. 1: enable 0: disable."]
    #[inline(always)]
    pub fn fread_quad(&self) -> FREAD_QUAD_R {
        FREAD_QUAD_R::new(((self.bits >> 20) & 1) != 0)
    }
    #[doc = "Bit 21 - Write protect signal output when SPI is idle. 1: output high, 0: output low."]
    #[inline(always)]
    pub fn wp(&self) -> WP_R {
        WP_R::new(((self.bits >> 21) & 1) != 0)
    }
    #[doc = "Bit 23 - In the read operations address phase and read-data phase apply 2 signals. 1: enable 0: disable."]
    #[inline(always)]
    pub fn fread_dio(&self) -> FREAD_DIO_R {
        FREAD_DIO_R::new(((self.bits >> 23) & 1) != 0)
    }
    #[doc = "Bit 24 - In the read operations address phase and read-data phase apply 4 signals. 1: enable 0: disable."]
    #[inline(always)]
    pub fn fread_qio(&self) -> FREAD_QIO_R {
        FREAD_QIO_R::new(((self.bits >> 24) & 1) != 0)
    }
    #[doc = "Bit 30 - When accesses to flash, 1: the IE signals of pads connected to SPI_DQS are always 1. 0: Others."]
    #[inline(always)]
    pub fn dqs_ie_always_on(&self) -> DQS_IE_ALWAYS_ON_R {
        DQS_IE_ALWAYS_ON_R::new(((self.bits >> 30) & 1) != 0)
    }
    #[doc = "Bit 31 - When accesses to flash, 1: the IE signals of pads connected to SPI_IO\\[7:0\\] are always 1. 0: Others."]
    #[inline(always)]
    pub fn data_ie_always_on(&self) -> DATA_IE_ALWAYS_ON_R {
        DATA_IE_ALWAYS_ON_R::new(((self.bits >> 31) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("CTRL")
            .field("wdummy_dqs_always_out", &self.wdummy_dqs_always_out())
            .field("wdummy_always_out", &self.wdummy_always_out())
            .field("fdummy_rin", &self.fdummy_rin())
            .field("fdummy_wout", &self.fdummy_wout())
            .field("fdout_oct", &self.fdout_oct())
            .field("fdin_oct", &self.fdin_oct())
            .field("faddr_oct", &self.faddr_oct())
            .field("fcmd_quad", &self.fcmd_quad())
            .field("fcmd_oct", &self.fcmd_oct())
            .field("fastrd_mode", &self.fastrd_mode())
            .field("fread_dual", &self.fread_dual())
            .field("q_pol", &self.q_pol())
            .field("d_pol", &self.d_pol())
            .field("fread_quad", &self.fread_quad())
            .field("wp", &self.wp())
            .field("fread_dio", &self.fread_dio())
            .field("fread_qio", &self.fread_qio())
            .field("dqs_ie_always_on", &self.dqs_ie_always_on())
            .field("data_ie_always_on", &self.data_ie_always_on())
            .finish()
    }
}
impl W {
    #[doc = "Bit 1 - In the dummy phase of an MSPI write data transfer when accesses to flash, the level of SPI_IO\\[7:0\\] is output by the MSPI controller."]
    #[inline(always)]
    pub fn wdummy_always_out(&mut self) -> WDUMMY_ALWAYS_OUT_W<'_, CTRL_SPEC> {
        WDUMMY_ALWAYS_OUT_W::new(self, 1)
    }
    #[doc = "Bit 2 - In an MSPI read data transfer when accesses to flash, the level of SPI_IO\\[7:0\\] is output by the MSPI controller in the first half part of dummy phase. It is used to mask invalid SPI_DQS in the half part of dummy phase."]
    #[inline(always)]
    pub fn fdummy_rin(&mut self) -> FDUMMY_RIN_W<'_, CTRL_SPEC> {
        FDUMMY_RIN_W::new(self, 2)
    }
    #[doc = "Bit 3 - In an MSPI write data transfer when accesses to flash, the level of SPI_IO\\[7:0\\] is output by the MSPI controller in the second half part of dummy phase. It is used to pre-drive flash."]
    #[inline(always)]
    pub fn fdummy_wout(&mut self) -> FDUMMY_WOUT_W<'_, CTRL_SPEC> {
        FDUMMY_WOUT_W::new(self, 3)
    }
    #[doc = "Bit 8 - Apply 4 signals during command phase 1:enable 0: disable"]
    #[inline(always)]
    pub fn fcmd_quad(&mut self) -> FCMD_QUAD_W<'_, CTRL_SPEC> {
        FCMD_QUAD_W::new(self, 8)
    }
    #[doc = "Bit 13 - This bit enable the bits: SPI_MEM_FREAD_QIO, SPI_MEM_FREAD_DIO, SPI_MEM_FREAD_QOUT and SPI_MEM_FREAD_DOUT. 1: enable 0: disable."]
    #[inline(always)]
    pub fn fastrd_mode(&mut self) -> FASTRD_MODE_W<'_, CTRL_SPEC> {
        FASTRD_MODE_W::new(self, 13)
    }
    #[doc = "Bit 14 - In the read operations, read-data phase apply 2 signals. 1: enable 0: disable."]
    #[inline(always)]
    pub fn fread_dual(&mut self) -> FREAD_DUAL_W<'_, CTRL_SPEC> {
        FREAD_DUAL_W::new(self, 14)
    }
    #[doc = "Bit 18 - The bit is used to set MISO line polarity, 1: high 0, low"]
    #[inline(always)]
    pub fn q_pol(&mut self) -> Q_POL_W<'_, CTRL_SPEC> {
        Q_POL_W::new(self, 18)
    }
    #[doc = "Bit 19 - The bit is used to set MOSI line polarity, 1: high 0, low"]
    #[inline(always)]
    pub fn d_pol(&mut self) -> D_POL_W<'_, CTRL_SPEC> {
        D_POL_W::new(self, 19)
    }
    #[doc = "Bit 20 - In the read operations read-data phase apply 4 signals. 1: enable 0: disable."]
    #[inline(always)]
    pub fn fread_quad(&mut self) -> FREAD_QUAD_W<'_, CTRL_SPEC> {
        FREAD_QUAD_W::new(self, 20)
    }
    #[doc = "Bit 21 - Write protect signal output when SPI is idle. 1: output high, 0: output low."]
    #[inline(always)]
    pub fn wp(&mut self) -> WP_W<'_, CTRL_SPEC> {
        WP_W::new(self, 21)
    }
    #[doc = "Bit 23 - In the read operations address phase and read-data phase apply 2 signals. 1: enable 0: disable."]
    #[inline(always)]
    pub fn fread_dio(&mut self) -> FREAD_DIO_W<'_, CTRL_SPEC> {
        FREAD_DIO_W::new(self, 23)
    }
    #[doc = "Bit 24 - In the read operations address phase and read-data phase apply 4 signals. 1: enable 0: disable."]
    #[inline(always)]
    pub fn fread_qio(&mut self) -> FREAD_QIO_W<'_, CTRL_SPEC> {
        FREAD_QIO_W::new(self, 24)
    }
    #[doc = "Bit 31 - When accesses to flash, 1: the IE signals of pads connected to SPI_IO\\[7:0\\] are always 1. 0: Others."]
    #[inline(always)]
    pub fn data_ie_always_on(&mut self) -> DATA_IE_ALWAYS_ON_W<'_, CTRL_SPEC> {
        DATA_IE_ALWAYS_ON_W::new(self, 31)
    }
}
#[doc = "SPI0 control register.\n\nYou can [`read`](crate::Reg::read) this register and get [`ctrl::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`ctrl::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct CTRL_SPEC;
impl crate::RegisterSpec for CTRL_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`ctrl::R`](R) reader structure"]
impl crate::Readable for CTRL_SPEC {}
#[doc = "`write(|w| ..)` method takes [`ctrl::W`](W) writer structure"]
impl crate::Writable for CTRL_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets CTRL to value 0x802c_200c"]
impl crate::Resettable for CTRL_SPEC {
    const RESET_VALUE: u32 = 0x802c_200c;
}
