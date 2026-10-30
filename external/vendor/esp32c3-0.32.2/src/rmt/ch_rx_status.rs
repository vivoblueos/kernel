#[doc = "Register `CH%s_RX_STATUS` reader"]
pub type R = crate::R<CH_RX_STATUS_SPEC>;
#[doc = "Field `MEM_WADDR_EX` reader - reg_mem_waddr_ex_ch2."]
pub type MEM_WADDR_EX_R = crate::FieldReader<u16>;
#[doc = "Field `APB_MEM_RADDR` reader - reg_apb_mem_raddr_ch2."]
pub type APB_MEM_RADDR_R = crate::FieldReader<u16>;
#[doc = "Field `STATE` reader - reg_state_ch2."]
pub type STATE_R = crate::FieldReader;
#[doc = "Field `MEM_OWNER_ERR` reader - reg_mem_owner_err_ch2."]
pub type MEM_OWNER_ERR_R = crate::BitReader;
#[doc = "Field `MEM_FULL` reader - reg_mem_full_ch2."]
pub type MEM_FULL_R = crate::BitReader;
#[doc = "Field `APB_MEM_RD_ERR` reader - reg_apb_mem_rd_err_ch2."]
pub type APB_MEM_RD_ERR_R = crate::BitReader;
impl R {
    #[doc = "Bits 0:8 - reg_mem_waddr_ex_ch2."]
    #[inline(always)]
    pub fn mem_waddr_ex(&self) -> MEM_WADDR_EX_R {
        MEM_WADDR_EX_R::new((self.bits & 0x01ff) as u16)
    }
    #[doc = "Bits 12:20 - reg_apb_mem_raddr_ch2."]
    #[inline(always)]
    pub fn apb_mem_raddr(&self) -> APB_MEM_RADDR_R {
        APB_MEM_RADDR_R::new(((self.bits >> 12) & 0x01ff) as u16)
    }
    #[doc = "Bits 22:24 - reg_state_ch2."]
    #[inline(always)]
    pub fn state(&self) -> STATE_R {
        STATE_R::new(((self.bits >> 22) & 7) as u8)
    }
    #[doc = "Bit 25 - reg_mem_owner_err_ch2."]
    #[inline(always)]
    pub fn mem_owner_err(&self) -> MEM_OWNER_ERR_R {
        MEM_OWNER_ERR_R::new(((self.bits >> 25) & 1) != 0)
    }
    #[doc = "Bit 26 - reg_mem_full_ch2."]
    #[inline(always)]
    pub fn mem_full(&self) -> MEM_FULL_R {
        MEM_FULL_R::new(((self.bits >> 26) & 1) != 0)
    }
    #[doc = "Bit 27 - reg_apb_mem_rd_err_ch2."]
    #[inline(always)]
    pub fn apb_mem_rd_err(&self) -> APB_MEM_RD_ERR_R {
        APB_MEM_RD_ERR_R::new(((self.bits >> 27) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("CH_RX_STATUS")
            .field("mem_waddr_ex", &self.mem_waddr_ex())
            .field("apb_mem_raddr", &self.apb_mem_raddr())
            .field("state", &self.state())
            .field("mem_owner_err", &self.mem_owner_err())
            .field("mem_full", &self.mem_full())
            .field("apb_mem_rd_err", &self.apb_mem_rd_err())
            .finish()
    }
}
#[doc = "RMT_CH%sSTATUS_REG.\n\nYou can [`read`](crate::Reg::read) this register and get [`ch_rx_status::R`](R). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct CH_RX_STATUS_SPEC;
impl crate::RegisterSpec for CH_RX_STATUS_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`ch_rx_status::R`](R) reader structure"]
impl crate::Readable for CH_RX_STATUS_SPEC {}
#[doc = "`reset()` method sets CH%s_RX_STATUS to value 0"]
impl crate::Resettable for CH_RX_STATUS_SPEC {}
