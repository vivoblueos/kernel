#[doc = "Register `INT_CLR` writer"]
pub type W = crate::W<INT_CLR_SPEC>;
#[doc = "Field `RXFIFO_WM` writer - reg_rxfifo_wm_int_clr"]
pub type RXFIFO_WM_W<'a, REG> = crate::BitWriter1C<'a, REG>;
#[doc = "Field `TXFIFO_WM` writer - reg_txfifo_wm_int_clr"]
pub type TXFIFO_WM_W<'a, REG> = crate::BitWriter1C<'a, REG>;
#[doc = "Field `RXFIFO_OVF` writer - reg_rxfifo_ovf_int_clr"]
pub type RXFIFO_OVF_W<'a, REG> = crate::BitWriter1C<'a, REG>;
#[doc = "Field `END_DETECT` writer - reg_end_detect_int_clr"]
pub type END_DETECT_W<'a, REG> = crate::BitWriter1C<'a, REG>;
#[doc = "Field `BYTE_TRANS_DONE` writer - reg_byte_trans_done_int_clr"]
pub type BYTE_TRANS_DONE_W<'a, REG> = crate::BitWriter1C<'a, REG>;
#[doc = "Field `ARBITRATION_LOST` writer - reg_arbitration_lost_int_clr"]
pub type ARBITRATION_LOST_W<'a, REG> = crate::BitWriter1C<'a, REG>;
#[doc = "Field `MST_TXFIFO_UDF` writer - reg_mst_txfifo_udf_int_clr"]
pub type MST_TXFIFO_UDF_W<'a, REG> = crate::BitWriter1C<'a, REG>;
#[doc = "Field `TRANS_COMPLETE` writer - reg_trans_complete_int_clr"]
pub type TRANS_COMPLETE_W<'a, REG> = crate::BitWriter1C<'a, REG>;
#[doc = "Field `TIME_OUT` writer - reg_time_out_int_clr"]
pub type TIME_OUT_W<'a, REG> = crate::BitWriter1C<'a, REG>;
#[doc = "Field `TRANS_START` writer - reg_trans_start_int_clr"]
pub type TRANS_START_W<'a, REG> = crate::BitWriter1C<'a, REG>;
#[doc = "Field `NACK` writer - reg_nack_int_clr"]
pub type NACK_W<'a, REG> = crate::BitWriter1C<'a, REG>;
#[doc = "Field `TXFIFO_OVF` writer - reg_txfifo_ovf_int_clr"]
pub type TXFIFO_OVF_W<'a, REG> = crate::BitWriter1C<'a, REG>;
#[doc = "Field `RXFIFO_UDF` writer - reg_rxfifo_udf_int_clr"]
pub type RXFIFO_UDF_W<'a, REG> = crate::BitWriter1C<'a, REG>;
#[doc = "Field `SCL_ST_TO` writer - reg_scl_st_to_int_clr"]
pub type SCL_ST_TO_W<'a, REG> = crate::BitWriter1C<'a, REG>;
#[doc = "Field `SCL_MAIN_ST_TO` writer - reg_scl_main_st_to_int_clr"]
pub type SCL_MAIN_ST_TO_W<'a, REG> = crate::BitWriter1C<'a, REG>;
#[doc = "Field `DET_START` writer - reg_det_start_int_clr"]
pub type DET_START_W<'a, REG> = crate::BitWriter1C<'a, REG>;
#[doc = "Field `SLAVE_STRETCH` writer - reg_slave_stretch_int_clr"]
pub type SLAVE_STRETCH_W<'a, REG> = crate::BitWriter1C<'a, REG>;
#[doc = "Field `GENERAL_CALL` writer - reg_general_call_int_clr"]
pub type GENERAL_CALL_W<'a, REG> = crate::BitWriter1C<'a, REG>;
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for crate::generic::Reg<INT_CLR_SPEC> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "(not readable)")
    }
}
impl W {
    #[doc = "Bit 0 - reg_rxfifo_wm_int_clr"]
    #[inline(always)]
    pub fn rxfifo_wm(&mut self) -> RXFIFO_WM_W<'_, INT_CLR_SPEC> {
        RXFIFO_WM_W::new(self, 0)
    }
    #[doc = "Bit 1 - reg_txfifo_wm_int_clr"]
    #[inline(always)]
    pub fn txfifo_wm(&mut self) -> TXFIFO_WM_W<'_, INT_CLR_SPEC> {
        TXFIFO_WM_W::new(self, 1)
    }
    #[doc = "Bit 2 - reg_rxfifo_ovf_int_clr"]
    #[inline(always)]
    pub fn rxfifo_ovf(&mut self) -> RXFIFO_OVF_W<'_, INT_CLR_SPEC> {
        RXFIFO_OVF_W::new(self, 2)
    }
    #[doc = "Bit 3 - reg_end_detect_int_clr"]
    #[inline(always)]
    pub fn end_detect(&mut self) -> END_DETECT_W<'_, INT_CLR_SPEC> {
        END_DETECT_W::new(self, 3)
    }
    #[doc = "Bit 4 - reg_byte_trans_done_int_clr"]
    #[inline(always)]
    pub fn byte_trans_done(&mut self) -> BYTE_TRANS_DONE_W<'_, INT_CLR_SPEC> {
        BYTE_TRANS_DONE_W::new(self, 4)
    }
    #[doc = "Bit 5 - reg_arbitration_lost_int_clr"]
    #[inline(always)]
    pub fn arbitration_lost(&mut self) -> ARBITRATION_LOST_W<'_, INT_CLR_SPEC> {
        ARBITRATION_LOST_W::new(self, 5)
    }
    #[doc = "Bit 6 - reg_mst_txfifo_udf_int_clr"]
    #[inline(always)]
    pub fn mst_txfifo_udf(&mut self) -> MST_TXFIFO_UDF_W<'_, INT_CLR_SPEC> {
        MST_TXFIFO_UDF_W::new(self, 6)
    }
    #[doc = "Bit 7 - reg_trans_complete_int_clr"]
    #[inline(always)]
    pub fn trans_complete(&mut self) -> TRANS_COMPLETE_W<'_, INT_CLR_SPEC> {
        TRANS_COMPLETE_W::new(self, 7)
    }
    #[doc = "Bit 8 - reg_time_out_int_clr"]
    #[inline(always)]
    pub fn time_out(&mut self) -> TIME_OUT_W<'_, INT_CLR_SPEC> {
        TIME_OUT_W::new(self, 8)
    }
    #[doc = "Bit 9 - reg_trans_start_int_clr"]
    #[inline(always)]
    pub fn trans_start(&mut self) -> TRANS_START_W<'_, INT_CLR_SPEC> {
        TRANS_START_W::new(self, 9)
    }
    #[doc = "Bit 10 - reg_nack_int_clr"]
    #[inline(always)]
    pub fn nack(&mut self) -> NACK_W<'_, INT_CLR_SPEC> {
        NACK_W::new(self, 10)
    }
    #[doc = "Bit 11 - reg_txfifo_ovf_int_clr"]
    #[inline(always)]
    pub fn txfifo_ovf(&mut self) -> TXFIFO_OVF_W<'_, INT_CLR_SPEC> {
        TXFIFO_OVF_W::new(self, 11)
    }
    #[doc = "Bit 12 - reg_rxfifo_udf_int_clr"]
    #[inline(always)]
    pub fn rxfifo_udf(&mut self) -> RXFIFO_UDF_W<'_, INT_CLR_SPEC> {
        RXFIFO_UDF_W::new(self, 12)
    }
    #[doc = "Bit 13 - reg_scl_st_to_int_clr"]
    #[inline(always)]
    pub fn scl_st_to(&mut self) -> SCL_ST_TO_W<'_, INT_CLR_SPEC> {
        SCL_ST_TO_W::new(self, 13)
    }
    #[doc = "Bit 14 - reg_scl_main_st_to_int_clr"]
    #[inline(always)]
    pub fn scl_main_st_to(&mut self) -> SCL_MAIN_ST_TO_W<'_, INT_CLR_SPEC> {
        SCL_MAIN_ST_TO_W::new(self, 14)
    }
    #[doc = "Bit 15 - reg_det_start_int_clr"]
    #[inline(always)]
    pub fn det_start(&mut self) -> DET_START_W<'_, INT_CLR_SPEC> {
        DET_START_W::new(self, 15)
    }
    #[doc = "Bit 16 - reg_slave_stretch_int_clr"]
    #[inline(always)]
    pub fn slave_stretch(&mut self) -> SLAVE_STRETCH_W<'_, INT_CLR_SPEC> {
        SLAVE_STRETCH_W::new(self, 16)
    }
    #[doc = "Bit 17 - reg_general_call_int_clr"]
    #[inline(always)]
    pub fn general_call(&mut self) -> GENERAL_CALL_W<'_, INT_CLR_SPEC> {
        GENERAL_CALL_W::new(self, 17)
    }
}
#[doc = "I2C_INT_CLR_REG\n\nYou can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`int_clr::W`](W). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct INT_CLR_SPEC;
impl crate::RegisterSpec for INT_CLR_SPEC {
    type Ux = u32;
}
#[doc = "`write(|w| ..)` method takes [`int_clr::W`](W) writer structure"]
impl crate::Writable for INT_CLR_SPEC {
    type Safety = crate::Unsafe;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0x0003_ffff;
}
#[doc = "`reset()` method sets INT_CLR to value 0"]
impl crate::Resettable for INT_CLR_SPEC {}
