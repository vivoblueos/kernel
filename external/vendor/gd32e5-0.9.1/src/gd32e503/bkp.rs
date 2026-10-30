#[repr(C)]
#[doc = "Register block"]
pub struct RegisterBlock {
    _reserved0: [u8; 0x04],
    data0: Data0,
    _reserved1: [u8; 0x02],
    data1: Data1,
    _reserved2: [u8; 0x02],
    data2: Data2,
    _reserved3: [u8; 0x02],
    data3: Data3,
    _reserved4: [u8; 0x02],
    data4: Data4,
    _reserved5: [u8; 0x02],
    data5: Data5,
    _reserved6: [u8; 0x02],
    data6: Data6,
    _reserved7: [u8; 0x02],
    data7: Data7,
    _reserved8: [u8; 0x02],
    data8: Data8,
    _reserved9: [u8; 0x02],
    data9: Data9,
    _reserved10: [u8; 0x02],
    octl: Octl,
    _reserved11: [u8; 0x02],
    tpctl: Tpctl,
    _reserved12: [u8; 0x02],
    tpcs: Tpcs,
    _reserved13: [u8; 0x0a],
    data10: Data10,
    _reserved14: [u8; 0x02],
    data11: Data11,
    _reserved15: [u8; 0x02],
    data12: Data12,
    _reserved16: [u8; 0x02],
    data13: Data13,
    _reserved17: [u8; 0x02],
    data14: Data14,
    _reserved18: [u8; 0x02],
    data15: Data15,
    _reserved19: [u8; 0x02],
    data16: Data16,
    _reserved20: [u8; 0x02],
    data17: Data17,
    _reserved21: [u8; 0x02],
    data18: Data18,
    _reserved22: [u8; 0x02],
    data19: Data19,
    _reserved23: [u8; 0x02],
    data20: Data20,
    _reserved24: [u8; 0x02],
    data21: Data21,
    _reserved25: [u8; 0x02],
    data22: Data22,
    _reserved26: [u8; 0x02],
    data23: Data23,
    _reserved27: [u8; 0x02],
    data24: Data24,
    _reserved28: [u8; 0x02],
    data25: Data25,
    _reserved29: [u8; 0x02],
    data26: Data26,
    _reserved30: [u8; 0x02],
    data27: Data27,
    _reserved31: [u8; 0x02],
    data28: Data28,
    _reserved32: [u8; 0x02],
    data29: Data29,
    _reserved33: [u8; 0x02],
    data30: Data30,
    _reserved34: [u8; 0x02],
    data31: Data31,
    _reserved35: [u8; 0x02],
    data32: Data32,
    _reserved36: [u8; 0x02],
    data33: Data33,
    _reserved37: [u8; 0x02],
    data34: Data34,
    _reserved38: [u8; 0x02],
    data35: Data35,
    _reserved39: [u8; 0x02],
    data36: Data36,
    _reserved40: [u8; 0x02],
    data37: Data37,
    _reserved41: [u8; 0x02],
    data38: Data38,
    _reserved42: [u8; 0x02],
    data39: Data39,
    _reserved43: [u8; 0x02],
    data40: Data40,
    _reserved44: [u8; 0x02],
    data41: Data41,
}
impl RegisterBlock {
    #[doc = "0x04 - Backup data register 0"]
    #[inline(always)]
    pub const fn data0(&self) -> &Data0 {
        &self.data0
    }
    #[doc = "0x08 - Backup data register 1"]
    #[inline(always)]
    pub const fn data1(&self) -> &Data1 {
        &self.data1
    }
    #[doc = "0x0c - Backup data register 2"]
    #[inline(always)]
    pub const fn data2(&self) -> &Data2 {
        &self.data2
    }
    #[doc = "0x10 - Backup data register 3"]
    #[inline(always)]
    pub const fn data3(&self) -> &Data3 {
        &self.data3
    }
    #[doc = "0x14 - Backup data register 4"]
    #[inline(always)]
    pub const fn data4(&self) -> &Data4 {
        &self.data4
    }
    #[doc = "0x18 - Backup data register 5"]
    #[inline(always)]
    pub const fn data5(&self) -> &Data5 {
        &self.data5
    }
    #[doc = "0x1c - Backup data register 6"]
    #[inline(always)]
    pub const fn data6(&self) -> &Data6 {
        &self.data6
    }
    #[doc = "0x20 - Backup data register 7"]
    #[inline(always)]
    pub const fn data7(&self) -> &Data7 {
        &self.data7
    }
    #[doc = "0x24 - Backup data register 8"]
    #[inline(always)]
    pub const fn data8(&self) -> &Data8 {
        &self.data8
    }
    #[doc = "0x28 - Backup data register 9"]
    #[inline(always)]
    pub const fn data9(&self) -> &Data9 {
        &self.data9
    }
    #[doc = "0x2c - RTC signal output control register"]
    #[inline(always)]
    pub const fn octl(&self) -> &Octl {
        &self.octl
    }
    #[doc = "0x30 - Tamper pin control register"]
    #[inline(always)]
    pub const fn tpctl(&self) -> &Tpctl {
        &self.tpctl
    }
    #[doc = "0x34 - Tamper control and status register"]
    #[inline(always)]
    pub const fn tpcs(&self) -> &Tpcs {
        &self.tpcs
    }
    #[doc = "0x40 - Backup data register 10"]
    #[inline(always)]
    pub const fn data10(&self) -> &Data10 {
        &self.data10
    }
    #[doc = "0x44 - Backup data register 11"]
    #[inline(always)]
    pub const fn data11(&self) -> &Data11 {
        &self.data11
    }
    #[doc = "0x48 - Backup data register 12"]
    #[inline(always)]
    pub const fn data12(&self) -> &Data12 {
        &self.data12
    }
    #[doc = "0x4c - Backup data register 13"]
    #[inline(always)]
    pub const fn data13(&self) -> &Data13 {
        &self.data13
    }
    #[doc = "0x50 - Backup data register 14"]
    #[inline(always)]
    pub const fn data14(&self) -> &Data14 {
        &self.data14
    }
    #[doc = "0x54 - Backup data register 15"]
    #[inline(always)]
    pub const fn data15(&self) -> &Data15 {
        &self.data15
    }
    #[doc = "0x58 - Backup data register 16"]
    #[inline(always)]
    pub const fn data16(&self) -> &Data16 {
        &self.data16
    }
    #[doc = "0x5c - Backup data register 17"]
    #[inline(always)]
    pub const fn data17(&self) -> &Data17 {
        &self.data17
    }
    #[doc = "0x60 - Backup data register 18"]
    #[inline(always)]
    pub const fn data18(&self) -> &Data18 {
        &self.data18
    }
    #[doc = "0x64 - Backup data register 19"]
    #[inline(always)]
    pub const fn data19(&self) -> &Data19 {
        &self.data19
    }
    #[doc = "0x68 - Backup data register 20"]
    #[inline(always)]
    pub const fn data20(&self) -> &Data20 {
        &self.data20
    }
    #[doc = "0x6c - Backup data register 21"]
    #[inline(always)]
    pub const fn data21(&self) -> &Data21 {
        &self.data21
    }
    #[doc = "0x70 - Backup data register 22"]
    #[inline(always)]
    pub const fn data22(&self) -> &Data22 {
        &self.data22
    }
    #[doc = "0x74 - Backup data register 23"]
    #[inline(always)]
    pub const fn data23(&self) -> &Data23 {
        &self.data23
    }
    #[doc = "0x78 - Backup data register 24"]
    #[inline(always)]
    pub const fn data24(&self) -> &Data24 {
        &self.data24
    }
    #[doc = "0x7c - Backup data register 25"]
    #[inline(always)]
    pub const fn data25(&self) -> &Data25 {
        &self.data25
    }
    #[doc = "0x80 - Backup data register 26"]
    #[inline(always)]
    pub const fn data26(&self) -> &Data26 {
        &self.data26
    }
    #[doc = "0x84 - Backup data register 27"]
    #[inline(always)]
    pub const fn data27(&self) -> &Data27 {
        &self.data27
    }
    #[doc = "0x88 - Backup data register 28"]
    #[inline(always)]
    pub const fn data28(&self) -> &Data28 {
        &self.data28
    }
    #[doc = "0x8c - Backup data register 29"]
    #[inline(always)]
    pub const fn data29(&self) -> &Data29 {
        &self.data29
    }
    #[doc = "0x90 - Backup data register 30"]
    #[inline(always)]
    pub const fn data30(&self) -> &Data30 {
        &self.data30
    }
    #[doc = "0x94 - Backup data register 31"]
    #[inline(always)]
    pub const fn data31(&self) -> &Data31 {
        &self.data31
    }
    #[doc = "0x98 - Backup data register 32"]
    #[inline(always)]
    pub const fn data32(&self) -> &Data32 {
        &self.data32
    }
    #[doc = "0x9c - Backup data register 33"]
    #[inline(always)]
    pub const fn data33(&self) -> &Data33 {
        &self.data33
    }
    #[doc = "0xa0 - Backup data register 34"]
    #[inline(always)]
    pub const fn data34(&self) -> &Data34 {
        &self.data34
    }
    #[doc = "0xa4 - Backup data register 35"]
    #[inline(always)]
    pub const fn data35(&self) -> &Data35 {
        &self.data35
    }
    #[doc = "0xa8 - Backup data register 36"]
    #[inline(always)]
    pub const fn data36(&self) -> &Data36 {
        &self.data36
    }
    #[doc = "0xac - Backup data register 37"]
    #[inline(always)]
    pub const fn data37(&self) -> &Data37 {
        &self.data37
    }
    #[doc = "0xb0 - Backup data register 38"]
    #[inline(always)]
    pub const fn data38(&self) -> &Data38 {
        &self.data38
    }
    #[doc = "0xb4 - Backup data register 39"]
    #[inline(always)]
    pub const fn data39(&self) -> &Data39 {
        &self.data39
    }
    #[doc = "0xb8 - Backup data register 40"]
    #[inline(always)]
    pub const fn data40(&self) -> &Data40 {
        &self.data40
    }
    #[doc = "0xbc - Backup data register 41"]
    #[inline(always)]
    pub const fn data41(&self) -> &Data41 {
        &self.data41
    }
}
#[doc = "DATA0 (rw) register accessor: Backup data register 0\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`data0::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`data0::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@data0`]
module"]
#[doc(alias = "DATA0")]
pub type Data0 = crate::Reg<data0::Data0Spec>;
#[doc = "Backup data register 0"]
pub mod data0;
#[doc = "DATA1 (rw) register accessor: Backup data register 1\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`data1::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`data1::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@data1`]
module"]
#[doc(alias = "DATA1")]
pub type Data1 = crate::Reg<data1::Data1Spec>;
#[doc = "Backup data register 1"]
pub mod data1;
#[doc = "DATA2 (rw) register accessor: Backup data register 2\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`data2::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`data2::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@data2`]
module"]
#[doc(alias = "DATA2")]
pub type Data2 = crate::Reg<data2::Data2Spec>;
#[doc = "Backup data register 2"]
pub mod data2;
#[doc = "DATA3 (rw) register accessor: Backup data register 3\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`data3::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`data3::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@data3`]
module"]
#[doc(alias = "DATA3")]
pub type Data3 = crate::Reg<data3::Data3Spec>;
#[doc = "Backup data register 3"]
pub mod data3;
#[doc = "DATA4 (rw) register accessor: Backup data register 4\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`data4::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`data4::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@data4`]
module"]
#[doc(alias = "DATA4")]
pub type Data4 = crate::Reg<data4::Data4Spec>;
#[doc = "Backup data register 4"]
pub mod data4;
#[doc = "DATA5 (rw) register accessor: Backup data register 5\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`data5::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`data5::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@data5`]
module"]
#[doc(alias = "DATA5")]
pub type Data5 = crate::Reg<data5::Data5Spec>;
#[doc = "Backup data register 5"]
pub mod data5;
#[doc = "DATA6 (rw) register accessor: Backup data register 6\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`data6::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`data6::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@data6`]
module"]
#[doc(alias = "DATA6")]
pub type Data6 = crate::Reg<data6::Data6Spec>;
#[doc = "Backup data register 6"]
pub mod data6;
#[doc = "DATA7 (rw) register accessor: Backup data register 7\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`data7::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`data7::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@data7`]
module"]
#[doc(alias = "DATA7")]
pub type Data7 = crate::Reg<data7::Data7Spec>;
#[doc = "Backup data register 7"]
pub mod data7;
#[doc = "DATA8 (rw) register accessor: Backup data register 8\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`data8::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`data8::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@data8`]
module"]
#[doc(alias = "DATA8")]
pub type Data8 = crate::Reg<data8::Data8Spec>;
#[doc = "Backup data register 8"]
pub mod data8;
#[doc = "DATA9 (rw) register accessor: Backup data register 9\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`data9::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`data9::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@data9`]
module"]
#[doc(alias = "DATA9")]
pub type Data9 = crate::Reg<data9::Data9Spec>;
#[doc = "Backup data register 9"]
pub mod data9;
#[doc = "DATA10 (rw) register accessor: Backup data register 10\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`data10::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`data10::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@data10`]
module"]
#[doc(alias = "DATA10")]
pub type Data10 = crate::Reg<data10::Data10Spec>;
#[doc = "Backup data register 10"]
pub mod data10;
#[doc = "DATA11 (rw) register accessor: Backup data register 11\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`data11::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`data11::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@data11`]
module"]
#[doc(alias = "DATA11")]
pub type Data11 = crate::Reg<data11::Data11Spec>;
#[doc = "Backup data register 11"]
pub mod data11;
#[doc = "DATA12 (rw) register accessor: Backup data register 12\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`data12::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`data12::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@data12`]
module"]
#[doc(alias = "DATA12")]
pub type Data12 = crate::Reg<data12::Data12Spec>;
#[doc = "Backup data register 12"]
pub mod data12;
#[doc = "DATA13 (rw) register accessor: Backup data register 13\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`data13::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`data13::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@data13`]
module"]
#[doc(alias = "DATA13")]
pub type Data13 = crate::Reg<data13::Data13Spec>;
#[doc = "Backup data register 13"]
pub mod data13;
#[doc = "DATA14 (rw) register accessor: Backup data register 14\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`data14::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`data14::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@data14`]
module"]
#[doc(alias = "DATA14")]
pub type Data14 = crate::Reg<data14::Data14Spec>;
#[doc = "Backup data register 14"]
pub mod data14;
#[doc = "DATA15 (rw) register accessor: Backup data register 15\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`data15::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`data15::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@data15`]
module"]
#[doc(alias = "DATA15")]
pub type Data15 = crate::Reg<data15::Data15Spec>;
#[doc = "Backup data register 15"]
pub mod data15;
#[doc = "DATA16 (rw) register accessor: Backup data register 16\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`data16::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`data16::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@data16`]
module"]
#[doc(alias = "DATA16")]
pub type Data16 = crate::Reg<data16::Data16Spec>;
#[doc = "Backup data register 16"]
pub mod data16;
#[doc = "DATA17 (rw) register accessor: Backup data register 17\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`data17::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`data17::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@data17`]
module"]
#[doc(alias = "DATA17")]
pub type Data17 = crate::Reg<data17::Data17Spec>;
#[doc = "Backup data register 17"]
pub mod data17;
#[doc = "DATA18 (rw) register accessor: Backup data register 18\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`data18::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`data18::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@data18`]
module"]
#[doc(alias = "DATA18")]
pub type Data18 = crate::Reg<data18::Data18Spec>;
#[doc = "Backup data register 18"]
pub mod data18;
#[doc = "DATA19 (rw) register accessor: Backup data register 19\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`data19::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`data19::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@data19`]
module"]
#[doc(alias = "DATA19")]
pub type Data19 = crate::Reg<data19::Data19Spec>;
#[doc = "Backup data register 19"]
pub mod data19;
#[doc = "DATA20 (rw) register accessor: Backup data register 20\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`data20::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`data20::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@data20`]
module"]
#[doc(alias = "DATA20")]
pub type Data20 = crate::Reg<data20::Data20Spec>;
#[doc = "Backup data register 20"]
pub mod data20;
#[doc = "DATA21 (rw) register accessor: Backup data register 21\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`data21::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`data21::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@data21`]
module"]
#[doc(alias = "DATA21")]
pub type Data21 = crate::Reg<data21::Data21Spec>;
#[doc = "Backup data register 21"]
pub mod data21;
#[doc = "DATA22 (rw) register accessor: Backup data register 22\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`data22::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`data22::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@data22`]
module"]
#[doc(alias = "DATA22")]
pub type Data22 = crate::Reg<data22::Data22Spec>;
#[doc = "Backup data register 22"]
pub mod data22;
#[doc = "DATA23 (rw) register accessor: Backup data register 23\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`data23::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`data23::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@data23`]
module"]
#[doc(alias = "DATA23")]
pub type Data23 = crate::Reg<data23::Data23Spec>;
#[doc = "Backup data register 23"]
pub mod data23;
#[doc = "DATA24 (rw) register accessor: Backup data register 24\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`data24::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`data24::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@data24`]
module"]
#[doc(alias = "DATA24")]
pub type Data24 = crate::Reg<data24::Data24Spec>;
#[doc = "Backup data register 24"]
pub mod data24;
#[doc = "DATA25 (rw) register accessor: Backup data register 25\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`data25::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`data25::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@data25`]
module"]
#[doc(alias = "DATA25")]
pub type Data25 = crate::Reg<data25::Data25Spec>;
#[doc = "Backup data register 25"]
pub mod data25;
#[doc = "DATA26 (rw) register accessor: Backup data register 26\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`data26::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`data26::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@data26`]
module"]
#[doc(alias = "DATA26")]
pub type Data26 = crate::Reg<data26::Data26Spec>;
#[doc = "Backup data register 26"]
pub mod data26;
#[doc = "DATA27 (rw) register accessor: Backup data register 27\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`data27::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`data27::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@data27`]
module"]
#[doc(alias = "DATA27")]
pub type Data27 = crate::Reg<data27::Data27Spec>;
#[doc = "Backup data register 27"]
pub mod data27;
#[doc = "DATA28 (rw) register accessor: Backup data register 28\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`data28::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`data28::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@data28`]
module"]
#[doc(alias = "DATA28")]
pub type Data28 = crate::Reg<data28::Data28Spec>;
#[doc = "Backup data register 28"]
pub mod data28;
#[doc = "DATA29 (rw) register accessor: Backup data register 29\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`data29::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`data29::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@data29`]
module"]
#[doc(alias = "DATA29")]
pub type Data29 = crate::Reg<data29::Data29Spec>;
#[doc = "Backup data register 29"]
pub mod data29;
#[doc = "DATA30 (rw) register accessor: Backup data register 30\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`data30::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`data30::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@data30`]
module"]
#[doc(alias = "DATA30")]
pub type Data30 = crate::Reg<data30::Data30Spec>;
#[doc = "Backup data register 30"]
pub mod data30;
#[doc = "DATA31 (rw) register accessor: Backup data register 31\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`data31::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`data31::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@data31`]
module"]
#[doc(alias = "DATA31")]
pub type Data31 = crate::Reg<data31::Data31Spec>;
#[doc = "Backup data register 31"]
pub mod data31;
#[doc = "DATA32 (rw) register accessor: Backup data register 32\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`data32::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`data32::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@data32`]
module"]
#[doc(alias = "DATA32")]
pub type Data32 = crate::Reg<data32::Data32Spec>;
#[doc = "Backup data register 32"]
pub mod data32;
#[doc = "DATA33 (rw) register accessor: Backup data register 33\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`data33::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`data33::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@data33`]
module"]
#[doc(alias = "DATA33")]
pub type Data33 = crate::Reg<data33::Data33Spec>;
#[doc = "Backup data register 33"]
pub mod data33;
#[doc = "DATA34 (rw) register accessor: Backup data register 34\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`data34::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`data34::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@data34`]
module"]
#[doc(alias = "DATA34")]
pub type Data34 = crate::Reg<data34::Data34Spec>;
#[doc = "Backup data register 34"]
pub mod data34;
#[doc = "DATA35 (rw) register accessor: Backup data register 35\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`data35::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`data35::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@data35`]
module"]
#[doc(alias = "DATA35")]
pub type Data35 = crate::Reg<data35::Data35Spec>;
#[doc = "Backup data register 35"]
pub mod data35;
#[doc = "DATA36 (rw) register accessor: Backup data register 36\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`data36::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`data36::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@data36`]
module"]
#[doc(alias = "DATA36")]
pub type Data36 = crate::Reg<data36::Data36Spec>;
#[doc = "Backup data register 36"]
pub mod data36;
#[doc = "DATA37 (rw) register accessor: Backup data register 37\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`data37::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`data37::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@data37`]
module"]
#[doc(alias = "DATA37")]
pub type Data37 = crate::Reg<data37::Data37Spec>;
#[doc = "Backup data register 37"]
pub mod data37;
#[doc = "DATA38 (rw) register accessor: Backup data register 38\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`data38::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`data38::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@data38`]
module"]
#[doc(alias = "DATA38")]
pub type Data38 = crate::Reg<data38::Data38Spec>;
#[doc = "Backup data register 38"]
pub mod data38;
#[doc = "DATA39 (rw) register accessor: Backup data register 39\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`data39::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`data39::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@data39`]
module"]
#[doc(alias = "DATA39")]
pub type Data39 = crate::Reg<data39::Data39Spec>;
#[doc = "Backup data register 39"]
pub mod data39;
#[doc = "DATA40 (rw) register accessor: Backup data register 40\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`data40::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`data40::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@data40`]
module"]
#[doc(alias = "DATA40")]
pub type Data40 = crate::Reg<data40::Data40Spec>;
#[doc = "Backup data register 40"]
pub mod data40;
#[doc = "DATA41 (rw) register accessor: Backup data register 41\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`data41::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`data41::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@data41`]
module"]
#[doc(alias = "DATA41")]
pub type Data41 = crate::Reg<data41::Data41Spec>;
#[doc = "Backup data register 41"]
pub mod data41;
#[doc = "OCTL (rw) register accessor: RTC signal output control register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`octl::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`octl::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@octl`]
module"]
#[doc(alias = "OCTL")]
pub type Octl = crate::Reg<octl::OctlSpec>;
#[doc = "RTC signal output control register"]
pub mod octl;
#[doc = "TPCTL (rw) register accessor: Tamper pin control register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`tpctl::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`tpctl::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@tpctl`]
module"]
#[doc(alias = "TPCTL")]
pub type Tpctl = crate::Reg<tpctl::TpctlSpec>;
#[doc = "Tamper pin control register"]
pub mod tpctl;
#[doc = "TPCS (rw) register accessor: Tamper control and status register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`tpcs::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`tpcs::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@tpcs`]
module"]
#[doc(alias = "TPCS")]
pub type Tpcs = crate::Reg<tpcs::TpcsSpec>;
#[doc = "Tamper control and status register"]
pub mod tpcs;
