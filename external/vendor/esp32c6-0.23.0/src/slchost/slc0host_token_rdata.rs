#[doc = "Register `SLC0HOST_TOKEN_RDATA` reader"]
pub type R = crate::R<SLC0HOST_TOKEN_RDATA_SPEC>;
#[doc = "Field `SLC0_TOKEN0` reader - *******Description***********"]
pub type SLC0_TOKEN0_R = crate::FieldReader<u16>;
#[doc = "Field `SLC0_RX_PF_VALID` reader - *******Description***********"]
pub type SLC0_RX_PF_VALID_R = crate::BitReader;
#[doc = "Field `HOSTSLCHOST_SLC0_TOKEN1` reader - *******Description***********"]
pub type HOSTSLCHOST_SLC0_TOKEN1_R = crate::FieldReader<u16>;
#[doc = "Field `SLC0_RX_PF_EOF` reader - *******Description***********"]
pub type SLC0_RX_PF_EOF_R = crate::FieldReader;
impl R {
    #[doc = "Bits 0:11 - *******Description***********"]
    #[inline(always)]
    pub fn slc0_token0(&self) -> SLC0_TOKEN0_R {
        SLC0_TOKEN0_R::new((self.bits & 0x0fff) as u16)
    }
    #[doc = "Bit 12 - *******Description***********"]
    #[inline(always)]
    pub fn slc0_rx_pf_valid(&self) -> SLC0_RX_PF_VALID_R {
        SLC0_RX_PF_VALID_R::new(((self.bits >> 12) & 1) != 0)
    }
    #[doc = "Bits 16:27 - *******Description***********"]
    #[inline(always)]
    pub fn hostslchost_slc0_token1(&self) -> HOSTSLCHOST_SLC0_TOKEN1_R {
        HOSTSLCHOST_SLC0_TOKEN1_R::new(((self.bits >> 16) & 0x0fff) as u16)
    }
    #[doc = "Bits 28:31 - *******Description***********"]
    #[inline(always)]
    pub fn slc0_rx_pf_eof(&self) -> SLC0_RX_PF_EOF_R {
        SLC0_RX_PF_EOF_R::new(((self.bits >> 28) & 0x0f) as u8)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("SLC0HOST_TOKEN_RDATA")
            .field("slc0_token0", &self.slc0_token0())
            .field("slc0_rx_pf_valid", &self.slc0_rx_pf_valid())
            .field("hostslchost_slc0_token1", &self.hostslchost_slc0_token1())
            .field("slc0_rx_pf_eof", &self.slc0_rx_pf_eof())
            .finish()
    }
}
#[doc = "*******Description***********\n\nYou can [`read`](crate::Reg::read) this register and get [`slc0host_token_rdata::R`](R). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct SLC0HOST_TOKEN_RDATA_SPEC;
impl crate::RegisterSpec for SLC0HOST_TOKEN_RDATA_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`slc0host_token_rdata::R`](R) reader structure"]
impl crate::Readable for SLC0HOST_TOKEN_RDATA_SPEC {}
#[doc = "`reset()` method sets SLC0HOST_TOKEN_RDATA to value 0"]
impl crate::Resettable for SLC0HOST_TOKEN_RDATA_SPEC {}
