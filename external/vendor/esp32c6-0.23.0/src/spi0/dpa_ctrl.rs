#[doc = "Register `DPA_CTRL` reader"]
pub type R = crate::R<DPA_CTRL_SPEC>;
#[doc = "Register `DPA_CTRL` writer"]
pub type W = crate::W<DPA_CTRL_SPEC>;
#[doc = "Field `SPI_CRYPT_SECURITY_LEVEL` reader - Set the security level of spi mem cryption. 0: Shut off cryption DPA funtion. 1-7: The bigger the number is, the more secure the cryption is. (Note that the performance of cryption will decrease together with this number increasing)"]
pub type SPI_CRYPT_SECURITY_LEVEL_R = crate::FieldReader;
#[doc = "Field `SPI_CRYPT_SECURITY_LEVEL` writer - Set the security level of spi mem cryption. 0: Shut off cryption DPA funtion. 1-7: The bigger the number is, the more secure the cryption is. (Note that the performance of cryption will decrease together with this number increasing)"]
pub type SPI_CRYPT_SECURITY_LEVEL_W<'a, REG> = crate::FieldWriter<'a, REG, 3>;
#[doc = "Field `SPI_CRYPT_CALC_D_DPA_EN` reader - Only available when SPI_CRYPT_SECURITY_LEVEL is not 0. 1: Enable DPA in the calculation that using key 1 or key 2. 0: Enable DPA only in the calculation that using key 1."]
pub type SPI_CRYPT_CALC_D_DPA_EN_R = crate::BitReader;
#[doc = "Field `SPI_CRYPT_CALC_D_DPA_EN` writer - Only available when SPI_CRYPT_SECURITY_LEVEL is not 0. 1: Enable DPA in the calculation that using key 1 or key 2. 0: Enable DPA only in the calculation that using key 1."]
pub type SPI_CRYPT_CALC_D_DPA_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SPI_CRYPT_DPA_SELECT_REGISTER` reader - 1: MSPI XTS DPA clock gate is controlled by SPI_CRYPT_CALC_D_DPA_EN and SPI_CRYPT_SECURITY_LEVEL. 0: Controlled by efuse bits."]
pub type SPI_CRYPT_DPA_SELECT_REGISTER_R = crate::BitReader;
#[doc = "Field `SPI_CRYPT_DPA_SELECT_REGISTER` writer - 1: MSPI XTS DPA clock gate is controlled by SPI_CRYPT_CALC_D_DPA_EN and SPI_CRYPT_SECURITY_LEVEL. 0: Controlled by efuse bits."]
pub type SPI_CRYPT_DPA_SELECT_REGISTER_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bits 0:2 - Set the security level of spi mem cryption. 0: Shut off cryption DPA funtion. 1-7: The bigger the number is, the more secure the cryption is. (Note that the performance of cryption will decrease together with this number increasing)"]
    #[inline(always)]
    pub fn spi_crypt_security_level(&self) -> SPI_CRYPT_SECURITY_LEVEL_R {
        SPI_CRYPT_SECURITY_LEVEL_R::new((self.bits & 7) as u8)
    }
    #[doc = "Bit 3 - Only available when SPI_CRYPT_SECURITY_LEVEL is not 0. 1: Enable DPA in the calculation that using key 1 or key 2. 0: Enable DPA only in the calculation that using key 1."]
    #[inline(always)]
    pub fn spi_crypt_calc_d_dpa_en(&self) -> SPI_CRYPT_CALC_D_DPA_EN_R {
        SPI_CRYPT_CALC_D_DPA_EN_R::new(((self.bits >> 3) & 1) != 0)
    }
    #[doc = "Bit 4 - 1: MSPI XTS DPA clock gate is controlled by SPI_CRYPT_CALC_D_DPA_EN and SPI_CRYPT_SECURITY_LEVEL. 0: Controlled by efuse bits."]
    #[inline(always)]
    pub fn spi_crypt_dpa_select_register(&self) -> SPI_CRYPT_DPA_SELECT_REGISTER_R {
        SPI_CRYPT_DPA_SELECT_REGISTER_R::new(((self.bits >> 4) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("DPA_CTRL")
            .field("spi_crypt_security_level", &self.spi_crypt_security_level())
            .field("spi_crypt_calc_d_dpa_en", &self.spi_crypt_calc_d_dpa_en())
            .field(
                "spi_crypt_dpa_select_register",
                &self.spi_crypt_dpa_select_register(),
            )
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:2 - Set the security level of spi mem cryption. 0: Shut off cryption DPA funtion. 1-7: The bigger the number is, the more secure the cryption is. (Note that the performance of cryption will decrease together with this number increasing)"]
    #[inline(always)]
    pub fn spi_crypt_security_level(&mut self) -> SPI_CRYPT_SECURITY_LEVEL_W<'_, DPA_CTRL_SPEC> {
        SPI_CRYPT_SECURITY_LEVEL_W::new(self, 0)
    }
    #[doc = "Bit 3 - Only available when SPI_CRYPT_SECURITY_LEVEL is not 0. 1: Enable DPA in the calculation that using key 1 or key 2. 0: Enable DPA only in the calculation that using key 1."]
    #[inline(always)]
    pub fn spi_crypt_calc_d_dpa_en(&mut self) -> SPI_CRYPT_CALC_D_DPA_EN_W<'_, DPA_CTRL_SPEC> {
        SPI_CRYPT_CALC_D_DPA_EN_W::new(self, 3)
    }
    #[doc = "Bit 4 - 1: MSPI XTS DPA clock gate is controlled by SPI_CRYPT_CALC_D_DPA_EN and SPI_CRYPT_SECURITY_LEVEL. 0: Controlled by efuse bits."]
    #[inline(always)]
    pub fn spi_crypt_dpa_select_register(
        &mut self,
    ) -> SPI_CRYPT_DPA_SELECT_REGISTER_W<'_, DPA_CTRL_SPEC> {
        SPI_CRYPT_DPA_SELECT_REGISTER_W::new(self, 4)
    }
}
#[doc = "SPI memory cryption DPA register\n\nYou can [`read`](crate::Reg::read) this register and get [`dpa_ctrl::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`dpa_ctrl::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct DPA_CTRL_SPEC;
impl crate::RegisterSpec for DPA_CTRL_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`dpa_ctrl::R`](R) reader structure"]
impl crate::Readable for DPA_CTRL_SPEC {}
#[doc = "`write(|w| ..)` method takes [`dpa_ctrl::W`](W) writer structure"]
impl crate::Writable for DPA_CTRL_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets DPA_CTRL to value 0x0f"]
impl crate::Resettable for DPA_CTRL_SPEC {
    const RESET_VALUE: u32 = 0x0f;
}
