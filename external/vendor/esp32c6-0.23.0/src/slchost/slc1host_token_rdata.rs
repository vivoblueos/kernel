#[doc = "Register `SLC1HOST_TOKEN_RDATA` reader"]
pub type R = crate::R<SLC1HOST_TOKEN_RDATA_SPEC>;
#[doc = "Field `SLC1_TOKEN0` reader - *******Description***********"]
pub type SLC1_TOKEN0_R = crate::FieldReader<u16>;
#[doc = "Field `SLC1_RX_PF_VALID` reader - *******Description***********"]
pub type SLC1_RX_PF_VALID_R = crate::BitReader;
#[doc = "Field `HOSTSLCHOST_SLC1_TOKEN1` reader - *******Description***********"]
pub type HOSTSLCHOST_SLC1_TOKEN1_R = crate::FieldReader<u16>;
#[doc = "Field `SLC1_RX_PF_EOF` reader - *******Description***********"]
pub type SLC1_RX_PF_EOF_R = crate::FieldReader;
impl R {
    #[doc = "Bits 0:11 - *******Description***********"]
    #[inline(always)]
    pub fn slc1_token0(&self) -> SLC1_TOKEN0_R {
        SLC1_TOKEN0_R::new((self.bits & 0x0fff) as u16)
    }
    #[doc = "Bit 12 - *******Description***********"]
    #[inline(always)]
    pub fn slc1_rx_pf_valid(&self) -> SLC1_RX_PF_VALID_R {
        SLC1_RX_PF_VALID_R::new(((self.bits >> 12) & 1) != 0)
    }
    #[doc = "Bits 16:27 - *******Description***********"]
    #[inline(always)]
    pub fn hostslchost_slc1_token1(&self) -> HOSTSLCHOST_SLC1_TOKEN1_R {
        HOSTSLCHOST_SLC1_TOKEN1_R::new(((self.bits >> 16) & 0x0fff) as u16)
    }
    #[doc = "Bits 28:31 - *******Description***********"]
    #[inline(always)]
    pub fn slc1_rx_pf_eof(&self) -> SLC1_RX_PF_EOF_R {
        SLC1_RX_PF_EOF_R::new(((self.bits >> 28) & 0x0f) as u8)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("SLC1HOST_TOKEN_RDATA")
            .field("slc1_token0", &self.slc1_token0())
            .field("slc1_rx_pf_valid", &self.slc1_rx_pf_valid())
            .field("hostslchost_slc1_token1", &self.hostslchost_slc1_token1())
            .field("slc1_rx_pf_eof", &self.slc1_rx_pf_eof())
            .finish()
    }
}
#[doc = "*******Description***********\n\nYou can [`read`](crate::Reg::read) this register and get [`slc1host_token_rdata::R`](R). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct SLC1HOST_TOKEN_RDATA_SPEC;
impl crate::RegisterSpec for SLC1HOST_TOKEN_RDATA_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`slc1host_token_rdata::R`](R) reader structure"]
impl crate::Readable for SLC1HOST_TOKEN_RDATA_SPEC {}
#[doc = "`reset()` method sets SLC1HOST_TOKEN_RDATA to value 0"]
impl crate::Resettable for SLC1HOST_TOKEN_RDATA_SPEC {}
