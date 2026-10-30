#[repr(C)]
#[cfg_attr(feature = "impl-register-debug", derive(Debug))]
#[doc = "Cluster CH%s, containing CH*_EVT_ID, CH*_TASK_ID"]
pub struct CH {
    evt_id: EVT_ID,
    task_id: TASK_ID,
}
impl CH {
    #[doc = "0x00 - channel0 event id register"]
    #[inline(always)]
    pub const fn evt_id(&self) -> &EVT_ID {
        &self.evt_id
    }
    #[doc = "0x04 - channel0 task id register"]
    #[inline(always)]
    pub const fn task_id(&self) -> &TASK_ID {
        &self.task_id
    }
}
#[doc = "EVT_ID (rw) register accessor: channel0 event id register\n\nYou can [`read`](crate::Reg::read) this register and get [`evt_id::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`evt_id::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@evt_id`] module"]
pub type EVT_ID = crate::Reg<evt_id::EVT_ID_SPEC>;
#[doc = "channel0 event id register"]
pub mod evt_id;
#[doc = "TASK_ID (rw) register accessor: channel0 task id register\n\nYou can [`read`](crate::Reg::read) this register and get [`task_id::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`task_id::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@task_id`] module"]
pub type TASK_ID = crate::Reg<task_id::TASK_ID_SPEC>;
#[doc = "channel0 task id register"]
pub mod task_id;
