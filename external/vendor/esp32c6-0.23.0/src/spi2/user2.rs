#[doc = "Register `USER2` reader"]
pub type R = crate::R<USER2_SPEC>;
#[doc = "Register `USER2` writer"]
pub type W = crate::W<USER2_SPEC>;
#[doc = "Field `USR_COMMAND_VALUE` reader - The value of command. Can be configured in CONF state."]
pub type USR_COMMAND_VALUE_R = crate::FieldReader<u16>;
#[doc = "Field `USR_COMMAND_VALUE` writer - The value of command. Can be configured in CONF state."]
pub type USR_COMMAND_VALUE_W<'a, REG> = crate::FieldWriter<'a, REG, 16, u16>;
#[doc = "Field `MST_REMPTY_ERR_END_EN` reader - 1: SPI transfer is ended when SPI TX AFIFO read empty error is valid in GP-SPI master FD/HD-mode. 0: SPI transfer is not ended when SPI TX AFIFO read empty error is valid in GP-SPI master FD/HD-mode."]
pub type MST_REMPTY_ERR_END_EN_R = crate::BitReader;
#[doc = "Field `MST_REMPTY_ERR_END_EN` writer - 1: SPI transfer is ended when SPI TX AFIFO read empty error is valid in GP-SPI master FD/HD-mode. 0: SPI transfer is not ended when SPI TX AFIFO read empty error is valid in GP-SPI master FD/HD-mode."]
pub type MST_REMPTY_ERR_END_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `USR_COMMAND_BITLEN` reader - The length in bits of command phase. The register value shall be (bit_num-1). Can be configured in CONF state."]
pub type USR_COMMAND_BITLEN_R = crate::FieldReader;
#[doc = "Field `USR_COMMAND_BITLEN` writer - The length in bits of command phase. The register value shall be (bit_num-1). Can be configured in CONF state."]
pub type USR_COMMAND_BITLEN_W<'a, REG> = crate::FieldWriter<'a, REG, 4>;
impl R {
    #[doc = "Bits 0:15 - The value of command. Can be configured in CONF state."]
    #[inline(always)]
    pub fn usr_command_value(&self) -> USR_COMMAND_VALUE_R {
        USR_COMMAND_VALUE_R::new((self.bits & 0xffff) as u16)
    }
    #[doc = "Bit 27 - 1: SPI transfer is ended when SPI TX AFIFO read empty error is valid in GP-SPI master FD/HD-mode. 0: SPI transfer is not ended when SPI TX AFIFO read empty error is valid in GP-SPI master FD/HD-mode."]
    #[inline(always)]
    pub fn mst_rempty_err_end_en(&self) -> MST_REMPTY_ERR_END_EN_R {
        MST_REMPTY_ERR_END_EN_R::new(((self.bits >> 27) & 1) != 0)
    }
    #[doc = "Bits 28:31 - The length in bits of command phase. The register value shall be (bit_num-1). Can be configured in CONF state."]
    #[inline(always)]
    pub fn usr_command_bitlen(&self) -> USR_COMMAND_BITLEN_R {
        USR_COMMAND_BITLEN_R::new(((self.bits >> 28) & 0x0f) as u8)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("USER2")
            .field("usr_command_value", &self.usr_command_value())
            .field("mst_rempty_err_end_en", &self.mst_rempty_err_end_en())
            .field("usr_command_bitlen", &self.usr_command_bitlen())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:15 - The value of command. Can be configured in CONF state."]
    #[inline(always)]
    pub fn usr_command_value(&mut self) -> USR_COMMAND_VALUE_W<'_, USER2_SPEC> {
        USR_COMMAND_VALUE_W::new(self, 0)
    }
    #[doc = "Bit 27 - 1: SPI transfer is ended when SPI TX AFIFO read empty error is valid in GP-SPI master FD/HD-mode. 0: SPI transfer is not ended when SPI TX AFIFO read empty error is valid in GP-SPI master FD/HD-mode."]
    #[inline(always)]
    pub fn mst_rempty_err_end_en(&mut self) -> MST_REMPTY_ERR_END_EN_W<'_, USER2_SPEC> {
        MST_REMPTY_ERR_END_EN_W::new(self, 27)
    }
    #[doc = "Bits 28:31 - The length in bits of command phase. The register value shall be (bit_num-1). Can be configured in CONF state."]
    #[inline(always)]
    pub fn usr_command_bitlen(&mut self) -> USR_COMMAND_BITLEN_W<'_, USER2_SPEC> {
        USR_COMMAND_BITLEN_W::new(self, 28)
    }
}
#[doc = "SPI USER control register 2\n\nYou can [`read`](crate::Reg::read) this register and get [`user2::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`user2::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct USER2_SPEC;
impl crate::RegisterSpec for USER2_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`user2::R`](R) reader structure"]
impl crate::Readable for USER2_SPEC {}
#[doc = "`write(|w| ..)` method takes [`user2::W`](W) writer structure"]
impl crate::Writable for USER2_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets USER2 to value 0x7800_0000"]
impl crate::Resettable for USER2_SPEC {
    const RESET_VALUE: u32 = 0x7800_0000;
}
