#[doc = "Register `USER` reader"]
pub type R = crate::R<USER_SPEC>;
#[doc = "Register `USER` writer"]
pub type W = crate::W<USER_SPEC>;
#[doc = "Field `CK_OUT_EDGE` reader - the bit combined with spi_mem_mosi_delay_mode bits to set mosi signal delay mode."]
pub type CK_OUT_EDGE_R = crate::BitReader;
#[doc = "Field `CK_OUT_EDGE` writer - the bit combined with spi_mem_mosi_delay_mode bits to set mosi signal delay mode."]
pub type CK_OUT_EDGE_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `FWRITE_DUAL` reader - In the write operations read-data phase apply 2 signals"]
pub type FWRITE_DUAL_R = crate::BitReader;
#[doc = "Field `FWRITE_DUAL` writer - In the write operations read-data phase apply 2 signals"]
pub type FWRITE_DUAL_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `FWRITE_QUAD` reader - In the write operations read-data phase apply 4 signals"]
pub type FWRITE_QUAD_R = crate::BitReader;
#[doc = "Field `FWRITE_QUAD` writer - In the write operations read-data phase apply 4 signals"]
pub type FWRITE_QUAD_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `FWRITE_DIO` reader - In the write operations address phase and read-data phase apply 2 signals."]
pub type FWRITE_DIO_R = crate::BitReader;
#[doc = "Field `FWRITE_DIO` writer - In the write operations address phase and read-data phase apply 2 signals."]
pub type FWRITE_DIO_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `FWRITE_QIO` reader - In the write operations address phase and read-data phase apply 4 signals."]
pub type FWRITE_QIO_R = crate::BitReader;
#[doc = "Field `FWRITE_QIO` writer - In the write operations address phase and read-data phase apply 4 signals."]
pub type FWRITE_QIO_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `USR_MISO_HIGHPART` reader - read-data phase only access to high-part of the buffer spi_mem_w8~spi_mem_w15. 1: enable 0: disable."]
pub type USR_MISO_HIGHPART_R = crate::BitReader;
#[doc = "Field `USR_MOSI_HIGHPART` reader - write-data phase only access to high-part of the buffer spi_mem_w8~spi_mem_w15. 1: enable 0: disable."]
pub type USR_MOSI_HIGHPART_R = crate::BitReader;
#[doc = "Field `USR_DUMMY_IDLE` reader - SPI clock is disable in dummy phase when the bit is enable."]
pub type USR_DUMMY_IDLE_R = crate::BitReader;
#[doc = "Field `USR_DUMMY_IDLE` writer - SPI clock is disable in dummy phase when the bit is enable."]
pub type USR_DUMMY_IDLE_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `USR_MOSI` reader - This bit enable the write-data phase of an operation."]
pub type USR_MOSI_R = crate::BitReader;
#[doc = "Field `USR_MOSI` writer - This bit enable the write-data phase of an operation."]
pub type USR_MOSI_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `USR_MISO` reader - This bit enable the read-data phase of an operation."]
pub type USR_MISO_R = crate::BitReader;
#[doc = "Field `USR_MISO` writer - This bit enable the read-data phase of an operation."]
pub type USR_MISO_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `USR_DUMMY` reader - This bit enable the dummy phase of an operation."]
pub type USR_DUMMY_R = crate::BitReader;
#[doc = "Field `USR_DUMMY` writer - This bit enable the dummy phase of an operation."]
pub type USR_DUMMY_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `USR_ADDR` reader - This bit enable the address phase of an operation."]
pub type USR_ADDR_R = crate::BitReader;
#[doc = "Field `USR_ADDR` writer - This bit enable the address phase of an operation."]
pub type USR_ADDR_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `USR_COMMAND` reader - This bit enable the command phase of an operation."]
pub type USR_COMMAND_R = crate::BitReader;
#[doc = "Field `USR_COMMAND` writer - This bit enable the command phase of an operation."]
pub type USR_COMMAND_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 9 - the bit combined with spi_mem_mosi_delay_mode bits to set mosi signal delay mode."]
    #[inline(always)]
    pub fn ck_out_edge(&self) -> CK_OUT_EDGE_R {
        CK_OUT_EDGE_R::new(((self.bits >> 9) & 1) != 0)
    }
    #[doc = "Bit 12 - In the write operations read-data phase apply 2 signals"]
    #[inline(always)]
    pub fn fwrite_dual(&self) -> FWRITE_DUAL_R {
        FWRITE_DUAL_R::new(((self.bits >> 12) & 1) != 0)
    }
    #[doc = "Bit 13 - In the write operations read-data phase apply 4 signals"]
    #[inline(always)]
    pub fn fwrite_quad(&self) -> FWRITE_QUAD_R {
        FWRITE_QUAD_R::new(((self.bits >> 13) & 1) != 0)
    }
    #[doc = "Bit 14 - In the write operations address phase and read-data phase apply 2 signals."]
    #[inline(always)]
    pub fn fwrite_dio(&self) -> FWRITE_DIO_R {
        FWRITE_DIO_R::new(((self.bits >> 14) & 1) != 0)
    }
    #[doc = "Bit 15 - In the write operations address phase and read-data phase apply 4 signals."]
    #[inline(always)]
    pub fn fwrite_qio(&self) -> FWRITE_QIO_R {
        FWRITE_QIO_R::new(((self.bits >> 15) & 1) != 0)
    }
    #[doc = "Bit 24 - read-data phase only access to high-part of the buffer spi_mem_w8~spi_mem_w15. 1: enable 0: disable."]
    #[inline(always)]
    pub fn usr_miso_highpart(&self) -> USR_MISO_HIGHPART_R {
        USR_MISO_HIGHPART_R::new(((self.bits >> 24) & 1) != 0)
    }
    #[doc = "Bit 25 - write-data phase only access to high-part of the buffer spi_mem_w8~spi_mem_w15. 1: enable 0: disable."]
    #[inline(always)]
    pub fn usr_mosi_highpart(&self) -> USR_MOSI_HIGHPART_R {
        USR_MOSI_HIGHPART_R::new(((self.bits >> 25) & 1) != 0)
    }
    #[doc = "Bit 26 - SPI clock is disable in dummy phase when the bit is enable."]
    #[inline(always)]
    pub fn usr_dummy_idle(&self) -> USR_DUMMY_IDLE_R {
        USR_DUMMY_IDLE_R::new(((self.bits >> 26) & 1) != 0)
    }
    #[doc = "Bit 27 - This bit enable the write-data phase of an operation."]
    #[inline(always)]
    pub fn usr_mosi(&self) -> USR_MOSI_R {
        USR_MOSI_R::new(((self.bits >> 27) & 1) != 0)
    }
    #[doc = "Bit 28 - This bit enable the read-data phase of an operation."]
    #[inline(always)]
    pub fn usr_miso(&self) -> USR_MISO_R {
        USR_MISO_R::new(((self.bits >> 28) & 1) != 0)
    }
    #[doc = "Bit 29 - This bit enable the dummy phase of an operation."]
    #[inline(always)]
    pub fn usr_dummy(&self) -> USR_DUMMY_R {
        USR_DUMMY_R::new(((self.bits >> 29) & 1) != 0)
    }
    #[doc = "Bit 30 - This bit enable the address phase of an operation."]
    #[inline(always)]
    pub fn usr_addr(&self) -> USR_ADDR_R {
        USR_ADDR_R::new(((self.bits >> 30) & 1) != 0)
    }
    #[doc = "Bit 31 - This bit enable the command phase of an operation."]
    #[inline(always)]
    pub fn usr_command(&self) -> USR_COMMAND_R {
        USR_COMMAND_R::new(((self.bits >> 31) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("USER")
            .field("ck_out_edge", &self.ck_out_edge())
            .field("fwrite_dual", &self.fwrite_dual())
            .field("fwrite_quad", &self.fwrite_quad())
            .field("fwrite_dio", &self.fwrite_dio())
            .field("fwrite_qio", &self.fwrite_qio())
            .field("usr_miso_highpart", &self.usr_miso_highpart())
            .field("usr_mosi_highpart", &self.usr_mosi_highpart())
            .field("usr_dummy_idle", &self.usr_dummy_idle())
            .field("usr_mosi", &self.usr_mosi())
            .field("usr_miso", &self.usr_miso())
            .field("usr_dummy", &self.usr_dummy())
            .field("usr_addr", &self.usr_addr())
            .field("usr_command", &self.usr_command())
            .finish()
    }
}
impl W {
    #[doc = "Bit 9 - the bit combined with spi_mem_mosi_delay_mode bits to set mosi signal delay mode."]
    #[inline(always)]
    pub fn ck_out_edge(&mut self) -> CK_OUT_EDGE_W<'_, USER_SPEC> {
        CK_OUT_EDGE_W::new(self, 9)
    }
    #[doc = "Bit 12 - In the write operations read-data phase apply 2 signals"]
    #[inline(always)]
    pub fn fwrite_dual(&mut self) -> FWRITE_DUAL_W<'_, USER_SPEC> {
        FWRITE_DUAL_W::new(self, 12)
    }
    #[doc = "Bit 13 - In the write operations read-data phase apply 4 signals"]
    #[inline(always)]
    pub fn fwrite_quad(&mut self) -> FWRITE_QUAD_W<'_, USER_SPEC> {
        FWRITE_QUAD_W::new(self, 13)
    }
    #[doc = "Bit 14 - In the write operations address phase and read-data phase apply 2 signals."]
    #[inline(always)]
    pub fn fwrite_dio(&mut self) -> FWRITE_DIO_W<'_, USER_SPEC> {
        FWRITE_DIO_W::new(self, 14)
    }
    #[doc = "Bit 15 - In the write operations address phase and read-data phase apply 4 signals."]
    #[inline(always)]
    pub fn fwrite_qio(&mut self) -> FWRITE_QIO_W<'_, USER_SPEC> {
        FWRITE_QIO_W::new(self, 15)
    }
    #[doc = "Bit 26 - SPI clock is disable in dummy phase when the bit is enable."]
    #[inline(always)]
    pub fn usr_dummy_idle(&mut self) -> USR_DUMMY_IDLE_W<'_, USER_SPEC> {
        USR_DUMMY_IDLE_W::new(self, 26)
    }
    #[doc = "Bit 27 - This bit enable the write-data phase of an operation."]
    #[inline(always)]
    pub fn usr_mosi(&mut self) -> USR_MOSI_W<'_, USER_SPEC> {
        USR_MOSI_W::new(self, 27)
    }
    #[doc = "Bit 28 - This bit enable the read-data phase of an operation."]
    #[inline(always)]
    pub fn usr_miso(&mut self) -> USR_MISO_W<'_, USER_SPEC> {
        USR_MISO_W::new(self, 28)
    }
    #[doc = "Bit 29 - This bit enable the dummy phase of an operation."]
    #[inline(always)]
    pub fn usr_dummy(&mut self) -> USR_DUMMY_W<'_, USER_SPEC> {
        USR_DUMMY_W::new(self, 29)
    }
    #[doc = "Bit 30 - This bit enable the address phase of an operation."]
    #[inline(always)]
    pub fn usr_addr(&mut self) -> USR_ADDR_W<'_, USER_SPEC> {
        USR_ADDR_W::new(self, 30)
    }
    #[doc = "Bit 31 - This bit enable the command phase of an operation."]
    #[inline(always)]
    pub fn usr_command(&mut self) -> USR_COMMAND_W<'_, USER_SPEC> {
        USR_COMMAND_W::new(self, 31)
    }
}
#[doc = "SPI1 user register.\n\nYou can [`read`](crate::Reg::read) this register and get [`user::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`user::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct USER_SPEC;
impl crate::RegisterSpec for USER_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`user::R`](R) reader structure"]
impl crate::Readable for USER_SPEC {}
#[doc = "`write(|w| ..)` method takes [`user::W`](W) writer structure"]
impl crate::Writable for USER_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets USER to value 0x8000_0000"]
impl crate::Resettable for USER_SPEC {
    const RESET_VALUE: u32 = 0x8000_0000;
}
