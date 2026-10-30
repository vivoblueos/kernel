#[repr(C)]
#[cfg_attr(feature = "impl-register-debug", derive(Debug))]
#[doc = "Cluster INF%s, containing INF?_EXTEND_ADDR0, INF?_EXTEND_ADDR1, INF?_PAN_ID, INF?_SHORT_ADDR"]
pub struct INF {
    short_addr: SHORT_ADDR,
    pan_id: PAN_ID,
    extend_addr0: EXTEND_ADDR0,
    extend_addr1: EXTEND_ADDR1,
}
impl INF {
    #[doc = "0x00 - "]
    #[inline(always)]
    pub const fn short_addr(&self) -> &SHORT_ADDR {
        &self.short_addr
    }
    #[doc = "0x04 - "]
    #[inline(always)]
    pub const fn pan_id(&self) -> &PAN_ID {
        &self.pan_id
    }
    #[doc = "0x08 - "]
    #[inline(always)]
    pub const fn extend_addr0(&self) -> &EXTEND_ADDR0 {
        &self.extend_addr0
    }
    #[doc = "0x0c - "]
    #[inline(always)]
    pub const fn extend_addr1(&self) -> &EXTEND_ADDR1 {
        &self.extend_addr1
    }
}
#[doc = "EXTEND_ADDR0 (rw) register accessor: \n\nYou can [`read`](crate::Reg::read) this register and get [`extend_addr0::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`extend_addr0::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@extend_addr0`] module"]
pub type EXTEND_ADDR0 = crate::Reg<extend_addr0::EXTEND_ADDR0_SPEC>;
#[doc = ""]
pub mod extend_addr0;
#[doc = "EXTEND_ADDR1 (rw) register accessor: \n\nYou can [`read`](crate::Reg::read) this register and get [`extend_addr1::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`extend_addr1::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@extend_addr1`] module"]
pub type EXTEND_ADDR1 = crate::Reg<extend_addr1::EXTEND_ADDR1_SPEC>;
#[doc = ""]
pub mod extend_addr1;
#[doc = "PAN_ID (rw) register accessor: \n\nYou can [`read`](crate::Reg::read) this register and get [`pan_id::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`pan_id::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@pan_id`] module"]
pub type PAN_ID = crate::Reg<pan_id::PAN_ID_SPEC>;
#[doc = ""]
pub mod pan_id;
#[doc = "SHORT_ADDR (rw) register accessor: \n\nYou can [`read`](crate::Reg::read) this register and get [`short_addr::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`short_addr::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@short_addr`] module"]
pub type SHORT_ADDR = crate::Reg<short_addr::SHORT_ADDR_SPEC>;
#[doc = ""]
pub mod short_addr;
