#[repr(C)]
#[doc = "Register block"]
pub struct RegisterBlock {
    mac_fcth: MacFcth,
}
impl RegisterBlock {
    #[doc = "0x00 - Ethernet MAC flow control threshold register"]
    #[inline(always)]
    pub const fn mac_fcth(&self) -> &MacFcth {
        &self.mac_fcth
    }
}
#[doc = "MAC_FCTH (rw) register accessor: Ethernet MAC flow control threshold register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`mac_fcth::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`mac_fcth::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@mac_fcth`]
module"]
#[doc(alias = "MAC_FCTH")]
pub type MacFcth = crate::Reg<mac_fcth::MacFcthSpec>;
#[doc = "Ethernet MAC flow control threshold register"]
pub mod mac_fcth;
