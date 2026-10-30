#[doc = "Register `SLC0HOST_INT_CLR` writer"]
pub type W = crate::W<SLC0HOST_INT_CLR_SPEC>;
#[doc = "Field `SLC0_TOHOST_BIT0_INT_CLR` writer - *******Description***********"]
pub type SLC0_TOHOST_BIT0_INT_CLR_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SLC0_TOHOST_BIT1_INT_CLR` writer - *******Description***********"]
pub type SLC0_TOHOST_BIT1_INT_CLR_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SLC0_TOHOST_BIT2_INT_CLR` writer - *******Description***********"]
pub type SLC0_TOHOST_BIT2_INT_CLR_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SLC0_TOHOST_BIT3_INT_CLR` writer - *******Description***********"]
pub type SLC0_TOHOST_BIT3_INT_CLR_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SLC0_TOHOST_BIT4_INT_CLR` writer - *******Description***********"]
pub type SLC0_TOHOST_BIT4_INT_CLR_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SLC0_TOHOST_BIT5_INT_CLR` writer - *******Description***********"]
pub type SLC0_TOHOST_BIT5_INT_CLR_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SLC0_TOHOST_BIT6_INT_CLR` writer - *******Description***********"]
pub type SLC0_TOHOST_BIT6_INT_CLR_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SLC0_TOHOST_BIT7_INT_CLR` writer - *******Description***********"]
pub type SLC0_TOHOST_BIT7_INT_CLR_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SLC0_TOKEN0_1TO0_INT_CLR` writer - *******Description***********"]
pub type SLC0_TOKEN0_1TO0_INT_CLR_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SLC0_TOKEN1_1TO0_INT_CLR` writer - *******Description***********"]
pub type SLC0_TOKEN1_1TO0_INT_CLR_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SLC0_TOKEN0_0TO1_INT_CLR` writer - *******Description***********"]
pub type SLC0_TOKEN0_0TO1_INT_CLR_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SLC0_TOKEN1_0TO1_INT_CLR` writer - *******Description***********"]
pub type SLC0_TOKEN1_0TO1_INT_CLR_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SLC0HOST_RX_SOF_INT_CLR` writer - *******Description***********"]
pub type SLC0HOST_RX_SOF_INT_CLR_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SLC0HOST_RX_EOF_INT_CLR` writer - *******Description***********"]
pub type SLC0HOST_RX_EOF_INT_CLR_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SLC0HOST_RX_START_INT_CLR` writer - *******Description***********"]
pub type SLC0HOST_RX_START_INT_CLR_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SLC0HOST_TX_START_INT_CLR` writer - *******Description***********"]
pub type SLC0HOST_TX_START_INT_CLR_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SLC0_RX_UDF_INT_CLR` writer - *******Description***********"]
pub type SLC0_RX_UDF_INT_CLR_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SLC0_TX_OVF_INT_CLR` writer - *******Description***********"]
pub type SLC0_TX_OVF_INT_CLR_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SLC0_RX_PF_VALID_INT_CLR` writer - *******Description***********"]
pub type SLC0_RX_PF_VALID_INT_CLR_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SLC0_EXT_BIT0_INT_CLR` writer - *******Description***********"]
pub type SLC0_EXT_BIT0_INT_CLR_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SLC0_EXT_BIT1_INT_CLR` writer - *******Description***********"]
pub type SLC0_EXT_BIT1_INT_CLR_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SLC0_EXT_BIT2_INT_CLR` writer - *******Description***********"]
pub type SLC0_EXT_BIT2_INT_CLR_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SLC0_EXT_BIT3_INT_CLR` writer - *******Description***********"]
pub type SLC0_EXT_BIT3_INT_CLR_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SLC0_RX_NEW_PACKET_INT_CLR` writer - *******Description***********"]
pub type SLC0_RX_NEW_PACKET_INT_CLR_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SLC0_HOST_RD_RETRY_INT_CLR` writer - *******Description***********"]
pub type SLC0_HOST_RD_RETRY_INT_CLR_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `GPIO_SDIO_INT_CLR` writer - *******Description***********"]
pub type GPIO_SDIO_INT_CLR_W<'a, REG> = crate::BitWriter<'a, REG>;
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for crate::generic::Reg<SLC0HOST_INT_CLR_SPEC> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "(not readable)")
    }
}
impl W {
    #[doc = "Bit 0 - *******Description***********"]
    #[inline(always)]
    pub fn slc0_tohost_bit0_int_clr(
        &mut self,
    ) -> SLC0_TOHOST_BIT0_INT_CLR_W<'_, SLC0HOST_INT_CLR_SPEC> {
        SLC0_TOHOST_BIT0_INT_CLR_W::new(self, 0)
    }
    #[doc = "Bit 1 - *******Description***********"]
    #[inline(always)]
    pub fn slc0_tohost_bit1_int_clr(
        &mut self,
    ) -> SLC0_TOHOST_BIT1_INT_CLR_W<'_, SLC0HOST_INT_CLR_SPEC> {
        SLC0_TOHOST_BIT1_INT_CLR_W::new(self, 1)
    }
    #[doc = "Bit 2 - *******Description***********"]
    #[inline(always)]
    pub fn slc0_tohost_bit2_int_clr(
        &mut self,
    ) -> SLC0_TOHOST_BIT2_INT_CLR_W<'_, SLC0HOST_INT_CLR_SPEC> {
        SLC0_TOHOST_BIT2_INT_CLR_W::new(self, 2)
    }
    #[doc = "Bit 3 - *******Description***********"]
    #[inline(always)]
    pub fn slc0_tohost_bit3_int_clr(
        &mut self,
    ) -> SLC0_TOHOST_BIT3_INT_CLR_W<'_, SLC0HOST_INT_CLR_SPEC> {
        SLC0_TOHOST_BIT3_INT_CLR_W::new(self, 3)
    }
    #[doc = "Bit 4 - *******Description***********"]
    #[inline(always)]
    pub fn slc0_tohost_bit4_int_clr(
        &mut self,
    ) -> SLC0_TOHOST_BIT4_INT_CLR_W<'_, SLC0HOST_INT_CLR_SPEC> {
        SLC0_TOHOST_BIT4_INT_CLR_W::new(self, 4)
    }
    #[doc = "Bit 5 - *******Description***********"]
    #[inline(always)]
    pub fn slc0_tohost_bit5_int_clr(
        &mut self,
    ) -> SLC0_TOHOST_BIT5_INT_CLR_W<'_, SLC0HOST_INT_CLR_SPEC> {
        SLC0_TOHOST_BIT5_INT_CLR_W::new(self, 5)
    }
    #[doc = "Bit 6 - *******Description***********"]
    #[inline(always)]
    pub fn slc0_tohost_bit6_int_clr(
        &mut self,
    ) -> SLC0_TOHOST_BIT6_INT_CLR_W<'_, SLC0HOST_INT_CLR_SPEC> {
        SLC0_TOHOST_BIT6_INT_CLR_W::new(self, 6)
    }
    #[doc = "Bit 7 - *******Description***********"]
    #[inline(always)]
    pub fn slc0_tohost_bit7_int_clr(
        &mut self,
    ) -> SLC0_TOHOST_BIT7_INT_CLR_W<'_, SLC0HOST_INT_CLR_SPEC> {
        SLC0_TOHOST_BIT7_INT_CLR_W::new(self, 7)
    }
    #[doc = "Bit 8 - *******Description***********"]
    #[inline(always)]
    pub fn slc0_token0_1to0_int_clr(
        &mut self,
    ) -> SLC0_TOKEN0_1TO0_INT_CLR_W<'_, SLC0HOST_INT_CLR_SPEC> {
        SLC0_TOKEN0_1TO0_INT_CLR_W::new(self, 8)
    }
    #[doc = "Bit 9 - *******Description***********"]
    #[inline(always)]
    pub fn slc0_token1_1to0_int_clr(
        &mut self,
    ) -> SLC0_TOKEN1_1TO0_INT_CLR_W<'_, SLC0HOST_INT_CLR_SPEC> {
        SLC0_TOKEN1_1TO0_INT_CLR_W::new(self, 9)
    }
    #[doc = "Bit 10 - *******Description***********"]
    #[inline(always)]
    pub fn slc0_token0_0to1_int_clr(
        &mut self,
    ) -> SLC0_TOKEN0_0TO1_INT_CLR_W<'_, SLC0HOST_INT_CLR_SPEC> {
        SLC0_TOKEN0_0TO1_INT_CLR_W::new(self, 10)
    }
    #[doc = "Bit 11 - *******Description***********"]
    #[inline(always)]
    pub fn slc0_token1_0to1_int_clr(
        &mut self,
    ) -> SLC0_TOKEN1_0TO1_INT_CLR_W<'_, SLC0HOST_INT_CLR_SPEC> {
        SLC0_TOKEN1_0TO1_INT_CLR_W::new(self, 11)
    }
    #[doc = "Bit 12 - *******Description***********"]
    #[inline(always)]
    pub fn slc0host_rx_sof_int_clr(
        &mut self,
    ) -> SLC0HOST_RX_SOF_INT_CLR_W<'_, SLC0HOST_INT_CLR_SPEC> {
        SLC0HOST_RX_SOF_INT_CLR_W::new(self, 12)
    }
    #[doc = "Bit 13 - *******Description***********"]
    #[inline(always)]
    pub fn slc0host_rx_eof_int_clr(
        &mut self,
    ) -> SLC0HOST_RX_EOF_INT_CLR_W<'_, SLC0HOST_INT_CLR_SPEC> {
        SLC0HOST_RX_EOF_INT_CLR_W::new(self, 13)
    }
    #[doc = "Bit 14 - *******Description***********"]
    #[inline(always)]
    pub fn slc0host_rx_start_int_clr(
        &mut self,
    ) -> SLC0HOST_RX_START_INT_CLR_W<'_, SLC0HOST_INT_CLR_SPEC> {
        SLC0HOST_RX_START_INT_CLR_W::new(self, 14)
    }
    #[doc = "Bit 15 - *******Description***********"]
    #[inline(always)]
    pub fn slc0host_tx_start_int_clr(
        &mut self,
    ) -> SLC0HOST_TX_START_INT_CLR_W<'_, SLC0HOST_INT_CLR_SPEC> {
        SLC0HOST_TX_START_INT_CLR_W::new(self, 15)
    }
    #[doc = "Bit 16 - *******Description***********"]
    #[inline(always)]
    pub fn slc0_rx_udf_int_clr(&mut self) -> SLC0_RX_UDF_INT_CLR_W<'_, SLC0HOST_INT_CLR_SPEC> {
        SLC0_RX_UDF_INT_CLR_W::new(self, 16)
    }
    #[doc = "Bit 17 - *******Description***********"]
    #[inline(always)]
    pub fn slc0_tx_ovf_int_clr(&mut self) -> SLC0_TX_OVF_INT_CLR_W<'_, SLC0HOST_INT_CLR_SPEC> {
        SLC0_TX_OVF_INT_CLR_W::new(self, 17)
    }
    #[doc = "Bit 18 - *******Description***********"]
    #[inline(always)]
    pub fn slc0_rx_pf_valid_int_clr(
        &mut self,
    ) -> SLC0_RX_PF_VALID_INT_CLR_W<'_, SLC0HOST_INT_CLR_SPEC> {
        SLC0_RX_PF_VALID_INT_CLR_W::new(self, 18)
    }
    #[doc = "Bit 19 - *******Description***********"]
    #[inline(always)]
    pub fn slc0_ext_bit0_int_clr(&mut self) -> SLC0_EXT_BIT0_INT_CLR_W<'_, SLC0HOST_INT_CLR_SPEC> {
        SLC0_EXT_BIT0_INT_CLR_W::new(self, 19)
    }
    #[doc = "Bit 20 - *******Description***********"]
    #[inline(always)]
    pub fn slc0_ext_bit1_int_clr(&mut self) -> SLC0_EXT_BIT1_INT_CLR_W<'_, SLC0HOST_INT_CLR_SPEC> {
        SLC0_EXT_BIT1_INT_CLR_W::new(self, 20)
    }
    #[doc = "Bit 21 - *******Description***********"]
    #[inline(always)]
    pub fn slc0_ext_bit2_int_clr(&mut self) -> SLC0_EXT_BIT2_INT_CLR_W<'_, SLC0HOST_INT_CLR_SPEC> {
        SLC0_EXT_BIT2_INT_CLR_W::new(self, 21)
    }
    #[doc = "Bit 22 - *******Description***********"]
    #[inline(always)]
    pub fn slc0_ext_bit3_int_clr(&mut self) -> SLC0_EXT_BIT3_INT_CLR_W<'_, SLC0HOST_INT_CLR_SPEC> {
        SLC0_EXT_BIT3_INT_CLR_W::new(self, 22)
    }
    #[doc = "Bit 23 - *******Description***********"]
    #[inline(always)]
    pub fn slc0_rx_new_packet_int_clr(
        &mut self,
    ) -> SLC0_RX_NEW_PACKET_INT_CLR_W<'_, SLC0HOST_INT_CLR_SPEC> {
        SLC0_RX_NEW_PACKET_INT_CLR_W::new(self, 23)
    }
    #[doc = "Bit 24 - *******Description***********"]
    #[inline(always)]
    pub fn slc0_host_rd_retry_int_clr(
        &mut self,
    ) -> SLC0_HOST_RD_RETRY_INT_CLR_W<'_, SLC0HOST_INT_CLR_SPEC> {
        SLC0_HOST_RD_RETRY_INT_CLR_W::new(self, 24)
    }
    #[doc = "Bit 25 - *******Description***********"]
    #[inline(always)]
    pub fn gpio_sdio_int_clr(&mut self) -> GPIO_SDIO_INT_CLR_W<'_, SLC0HOST_INT_CLR_SPEC> {
        GPIO_SDIO_INT_CLR_W::new(self, 25)
    }
}
#[doc = "*******Description***********\n\nYou can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`slc0host_int_clr::W`](W). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct SLC0HOST_INT_CLR_SPEC;
impl crate::RegisterSpec for SLC0HOST_INT_CLR_SPEC {
    type Ux = u32;
}
#[doc = "`write(|w| ..)` method takes [`slc0host_int_clr::W`](W) writer structure"]
impl crate::Writable for SLC0HOST_INT_CLR_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets SLC0HOST_INT_CLR to value 0"]
impl crate::Resettable for SLC0HOST_INT_CLR_SPEC {}
