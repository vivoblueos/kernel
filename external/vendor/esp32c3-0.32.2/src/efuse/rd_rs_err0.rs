#[doc = "Register `RD_RS_ERR0` reader"]
pub type R = crate::R<RD_RS_ERR0_SPEC>;
#[doc = "Field `MAC_SPI_8M_ERR_NUM` reader - The value of this signal means the number of error bytes."]
pub type MAC_SPI_8M_ERR_NUM_R = crate::FieldReader;
#[doc = "Field `MAC_SPI_8M_FAIL` reader - 0: Means no failure and that the data of MAC_SPI_8M is reliable 1: Means that programming user data failed and the number of error bytes is over 6."]
pub type MAC_SPI_8M_FAIL_R = crate::BitReader;
#[doc = "Field `SYS_PART1_NUM` reader - The value of this signal means the number of error bytes."]
pub type SYS_PART1_NUM_R = crate::FieldReader;
#[doc = "Field `SYS_PART1_FAIL` reader - 0: Means no failure and that the data of system part1 is reliable 1: Means that programming user data failed and the number of error bytes is over 6."]
pub type SYS_PART1_FAIL_R = crate::BitReader;
#[doc = "Field `USR_DATA_ERR_NUM` reader - The value of this signal means the number of error bytes."]
pub type USR_DATA_ERR_NUM_R = crate::FieldReader;
#[doc = "Field `USR_DATA_FAIL` reader - 0: Means no failure and that the user data is reliable 1: Means that programming user data failed and the number of error bytes is over 6."]
pub type USR_DATA_FAIL_R = crate::BitReader;
#[doc = "Field `KEY0_ERR_NUM` reader - The value of this signal means the number of error bytes."]
pub type KEY0_ERR_NUM_R = crate::FieldReader;
#[doc = "Field `KEY0_FAIL` reader - 0: Means no failure and that the data of key0 is reliable 1: Means that programming key0 failed and the number of error bytes is over 6."]
pub type KEY0_FAIL_R = crate::BitReader;
#[doc = "Field `KEY1_ERR_NUM` reader - The value of this signal means the number of error bytes."]
pub type KEY1_ERR_NUM_R = crate::FieldReader;
#[doc = "Field `KEY1_FAIL` reader - 0: Means no failure and that the data of key1 is reliable 1: Means that programming key1 failed and the number of error bytes is over 6."]
pub type KEY1_FAIL_R = crate::BitReader;
#[doc = "Field `KEY2_ERR_NUM` reader - The value of this signal means the number of error bytes."]
pub type KEY2_ERR_NUM_R = crate::FieldReader;
#[doc = "Field `KEY2_FAIL` reader - 0: Means no failure and that the data of key2 is reliable 1: Means that programming key2 failed and the number of error bytes is over 6."]
pub type KEY2_FAIL_R = crate::BitReader;
#[doc = "Field `KEY3_ERR_NUM` reader - The value of this signal means the number of error bytes."]
pub type KEY3_ERR_NUM_R = crate::FieldReader;
#[doc = "Field `KEY3_FAIL` reader - 0: Means no failure and that the data of key3 is reliable 1: Means that programming key3 failed and the number of error bytes is over 6."]
pub type KEY3_FAIL_R = crate::BitReader;
#[doc = "Field `KEY4_ERR_NUM` reader - The value of this signal means the number of error bytes."]
pub type KEY4_ERR_NUM_R = crate::FieldReader;
#[doc = "Field `KEY4_FAIL` reader - 0: Means no failure and that the data of key4 is reliable 1: Means that programming key4 failed and the number of error bytes is over 6."]
pub type KEY4_FAIL_R = crate::BitReader;
impl R {
    #[doc = "Bits 0:2 - The value of this signal means the number of error bytes."]
    #[inline(always)]
    pub fn mac_spi_8m_err_num(&self) -> MAC_SPI_8M_ERR_NUM_R {
        MAC_SPI_8M_ERR_NUM_R::new((self.bits & 7) as u8)
    }
    #[doc = "Bit 3 - 0: Means no failure and that the data of MAC_SPI_8M is reliable 1: Means that programming user data failed and the number of error bytes is over 6."]
    #[inline(always)]
    pub fn mac_spi_8m_fail(&self) -> MAC_SPI_8M_FAIL_R {
        MAC_SPI_8M_FAIL_R::new(((self.bits >> 3) & 1) != 0)
    }
    #[doc = "Bits 4:6 - The value of this signal means the number of error bytes."]
    #[inline(always)]
    pub fn sys_part1_num(&self) -> SYS_PART1_NUM_R {
        SYS_PART1_NUM_R::new(((self.bits >> 4) & 7) as u8)
    }
    #[doc = "Bit 7 - 0: Means no failure and that the data of system part1 is reliable 1: Means that programming user data failed and the number of error bytes is over 6."]
    #[inline(always)]
    pub fn sys_part1_fail(&self) -> SYS_PART1_FAIL_R {
        SYS_PART1_FAIL_R::new(((self.bits >> 7) & 1) != 0)
    }
    #[doc = "Bits 8:10 - The value of this signal means the number of error bytes."]
    #[inline(always)]
    pub fn usr_data_err_num(&self) -> USR_DATA_ERR_NUM_R {
        USR_DATA_ERR_NUM_R::new(((self.bits >> 8) & 7) as u8)
    }
    #[doc = "Bit 11 - 0: Means no failure and that the user data is reliable 1: Means that programming user data failed and the number of error bytes is over 6."]
    #[inline(always)]
    pub fn usr_data_fail(&self) -> USR_DATA_FAIL_R {
        USR_DATA_FAIL_R::new(((self.bits >> 11) & 1) != 0)
    }
    #[doc = "Bits 12:14 - The value of this signal means the number of error bytes."]
    #[inline(always)]
    pub fn key0_err_num(&self) -> KEY0_ERR_NUM_R {
        KEY0_ERR_NUM_R::new(((self.bits >> 12) & 7) as u8)
    }
    #[doc = "Bit 15 - 0: Means no failure and that the data of key0 is reliable 1: Means that programming key0 failed and the number of error bytes is over 6."]
    #[inline(always)]
    pub fn key0_fail(&self) -> KEY0_FAIL_R {
        KEY0_FAIL_R::new(((self.bits >> 15) & 1) != 0)
    }
    #[doc = "Bits 16:18 - The value of this signal means the number of error bytes."]
    #[inline(always)]
    pub fn key1_err_num(&self) -> KEY1_ERR_NUM_R {
        KEY1_ERR_NUM_R::new(((self.bits >> 16) & 7) as u8)
    }
    #[doc = "Bit 19 - 0: Means no failure and that the data of key1 is reliable 1: Means that programming key1 failed and the number of error bytes is over 6."]
    #[inline(always)]
    pub fn key1_fail(&self) -> KEY1_FAIL_R {
        KEY1_FAIL_R::new(((self.bits >> 19) & 1) != 0)
    }
    #[doc = "Bits 20:22 - The value of this signal means the number of error bytes."]
    #[inline(always)]
    pub fn key2_err_num(&self) -> KEY2_ERR_NUM_R {
        KEY2_ERR_NUM_R::new(((self.bits >> 20) & 7) as u8)
    }
    #[doc = "Bit 23 - 0: Means no failure and that the data of key2 is reliable 1: Means that programming key2 failed and the number of error bytes is over 6."]
    #[inline(always)]
    pub fn key2_fail(&self) -> KEY2_FAIL_R {
        KEY2_FAIL_R::new(((self.bits >> 23) & 1) != 0)
    }
    #[doc = "Bits 24:26 - The value of this signal means the number of error bytes."]
    #[inline(always)]
    pub fn key3_err_num(&self) -> KEY3_ERR_NUM_R {
        KEY3_ERR_NUM_R::new(((self.bits >> 24) & 7) as u8)
    }
    #[doc = "Bit 27 - 0: Means no failure and that the data of key3 is reliable 1: Means that programming key3 failed and the number of error bytes is over 6."]
    #[inline(always)]
    pub fn key3_fail(&self) -> KEY3_FAIL_R {
        KEY3_FAIL_R::new(((self.bits >> 27) & 1) != 0)
    }
    #[doc = "Bits 28:30 - The value of this signal means the number of error bytes."]
    #[inline(always)]
    pub fn key4_err_num(&self) -> KEY4_ERR_NUM_R {
        KEY4_ERR_NUM_R::new(((self.bits >> 28) & 7) as u8)
    }
    #[doc = "Bit 31 - 0: Means no failure and that the data of key4 is reliable 1: Means that programming key4 failed and the number of error bytes is over 6."]
    #[inline(always)]
    pub fn key4_fail(&self) -> KEY4_FAIL_R {
        KEY4_FAIL_R::new(((self.bits >> 31) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("RD_RS_ERR0")
            .field("mac_spi_8m_err_num", &self.mac_spi_8m_err_num())
            .field("mac_spi_8m_fail", &self.mac_spi_8m_fail())
            .field("sys_part1_num", &self.sys_part1_num())
            .field("sys_part1_fail", &self.sys_part1_fail())
            .field("usr_data_err_num", &self.usr_data_err_num())
            .field("usr_data_fail", &self.usr_data_fail())
            .field("key0_err_num", &self.key0_err_num())
            .field("key0_fail", &self.key0_fail())
            .field("key1_err_num", &self.key1_err_num())
            .field("key1_fail", &self.key1_fail())
            .field("key2_err_num", &self.key2_err_num())
            .field("key2_fail", &self.key2_fail())
            .field("key3_err_num", &self.key3_err_num())
            .field("key3_fail", &self.key3_fail())
            .field("key4_err_num", &self.key4_err_num())
            .field("key4_fail", &self.key4_fail())
            .finish()
    }
}
#[doc = "Programming error record register 0 of BLOCK1-10.\n\nYou can [`read`](crate::Reg::read) this register and get [`rd_rs_err0::R`](R). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct RD_RS_ERR0_SPEC;
impl crate::RegisterSpec for RD_RS_ERR0_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`rd_rs_err0::R`](R) reader structure"]
impl crate::Readable for RD_RS_ERR0_SPEC {}
#[doc = "`reset()` method sets RD_RS_ERR0 to value 0"]
impl crate::Resettable for RD_RS_ERR0_SPEC {}
