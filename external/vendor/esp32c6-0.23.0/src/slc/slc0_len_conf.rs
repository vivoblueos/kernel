#[doc = "Register `SLC0_LEN_CONF` writer"]
pub type W = crate::W<SLC0_LEN_CONF_SPEC>;
#[doc = "Field `SDIO_SLC0_LEN_WDATA` writer - Configures the length of the data that the slave wants to send."]
pub type SDIO_SLC0_LEN_WDATA_W<'a, REG> = crate::FieldWriter<'a, REG, 20, u32>;
#[doc = "Field `SDIO_SLC0_LEN_WR` writer - Configures this bit to 1 to write SDIO_SLC0_LEN_WDATA into SDIO_SLC0_LEN and SLCHOST_HOSTSLCHOST_SLC0_LEN."]
pub type SDIO_SLC0_LEN_WR_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SDIO_SLC0_LEN_INC` writer - Configures this bit to 1 to add 1 to SDIO_SLC0_LEN and SLCHOST_HOSTSLCHOST_SLC0_LEN."]
pub type SDIO_SLC0_LEN_INC_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SDIO_SLC0_LEN_INC_MORE` writer - Configures this bit to 1 to add the value of SDIO_SLC0_LEN_WDATA to SDIO_SLC0_LEN and SLCHOST_HOSTSLCHOST_SLC0_LEN."]
pub type SDIO_SLC0_LEN_INC_MORE_W<'a, REG> = crate::BitWriter<'a, REG>;
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for crate::generic::Reg<SLC0_LEN_CONF_SPEC> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "(not readable)")
    }
}
impl W {
    #[doc = "Bits 0:19 - Configures the length of the data that the slave wants to send."]
    #[inline(always)]
    pub fn sdio_slc0_len_wdata(&mut self) -> SDIO_SLC0_LEN_WDATA_W<'_, SLC0_LEN_CONF_SPEC> {
        SDIO_SLC0_LEN_WDATA_W::new(self, 0)
    }
    #[doc = "Bit 20 - Configures this bit to 1 to write SDIO_SLC0_LEN_WDATA into SDIO_SLC0_LEN and SLCHOST_HOSTSLCHOST_SLC0_LEN."]
    #[inline(always)]
    pub fn sdio_slc0_len_wr(&mut self) -> SDIO_SLC0_LEN_WR_W<'_, SLC0_LEN_CONF_SPEC> {
        SDIO_SLC0_LEN_WR_W::new(self, 20)
    }
    #[doc = "Bit 21 - Configures this bit to 1 to add 1 to SDIO_SLC0_LEN and SLCHOST_HOSTSLCHOST_SLC0_LEN."]
    #[inline(always)]
    pub fn sdio_slc0_len_inc(&mut self) -> SDIO_SLC0_LEN_INC_W<'_, SLC0_LEN_CONF_SPEC> {
        SDIO_SLC0_LEN_INC_W::new(self, 21)
    }
    #[doc = "Bit 22 - Configures this bit to 1 to add the value of SDIO_SLC0_LEN_WDATA to SDIO_SLC0_LEN and SLCHOST_HOSTSLCHOST_SLC0_LEN."]
    #[inline(always)]
    pub fn sdio_slc0_len_inc_more(&mut self) -> SDIO_SLC0_LEN_INC_MORE_W<'_, SLC0_LEN_CONF_SPEC> {
        SDIO_SLC0_LEN_INC_MORE_W::new(self, 22)
    }
}
#[doc = "Length control of transmitting packets\n\nYou can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`slc0_len_conf::W`](W). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct SLC0_LEN_CONF_SPEC;
impl crate::RegisterSpec for SLC0_LEN_CONF_SPEC {
    type Ux = u32;
}
#[doc = "`write(|w| ..)` method takes [`slc0_len_conf::W`](W) writer structure"]
impl crate::Writable for SLC0_LEN_CONF_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets SLC0_LEN_CONF to value 0x2000_0000"]
impl crate::Resettable for SLC0_LEN_CONF_SPEC {
    const RESET_VALUE: u32 = 0x2000_0000;
}
