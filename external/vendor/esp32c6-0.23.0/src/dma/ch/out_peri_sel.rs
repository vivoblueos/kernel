#[doc = "Register `OUT_PERI_SEL` reader"]
pub type R = crate::R<OUT_PERI_SEL_SPEC>;
#[doc = "Register `OUT_PERI_SEL` writer"]
pub type W = crate::W<OUT_PERI_SEL_SPEC>;
#[doc = "Field `PERI_OUT_SEL` reader - This register is used to select peripheral for Tx channel 0. 0:SPI2. 1: Dummy. 2: UHCI0. 3: I2S0. 4: Dummy. 5: Dummy. 6: AES. 7: SHA. 8: ADC_DAC. 9: Parallel_IO. 10~15: Dummy"]
pub type PERI_OUT_SEL_R = crate::FieldReader;
#[doc = "Field `PERI_OUT_SEL` writer - This register is used to select peripheral for Tx channel 0. 0:SPI2. 1: Dummy. 2: UHCI0. 3: I2S0. 4: Dummy. 5: Dummy. 6: AES. 7: SHA. 8: ADC_DAC. 9: Parallel_IO. 10~15: Dummy"]
pub type PERI_OUT_SEL_W<'a, REG> = crate::FieldWriter<'a, REG, 6>;
impl R {
    #[doc = "Bits 0:5 - This register is used to select peripheral for Tx channel 0. 0:SPI2. 1: Dummy. 2: UHCI0. 3: I2S0. 4: Dummy. 5: Dummy. 6: AES. 7: SHA. 8: ADC_DAC. 9: Parallel_IO. 10~15: Dummy"]
    #[inline(always)]
    pub fn peri_out_sel(&self) -> PERI_OUT_SEL_R {
        PERI_OUT_SEL_R::new((self.bits & 0x3f) as u8)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("OUT_PERI_SEL")
            .field("peri_out_sel", &self.peri_out_sel())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:5 - This register is used to select peripheral for Tx channel 0. 0:SPI2. 1: Dummy. 2: UHCI0. 3: I2S0. 4: Dummy. 5: Dummy. 6: AES. 7: SHA. 8: ADC_DAC. 9: Parallel_IO. 10~15: Dummy"]
    #[inline(always)]
    pub fn peri_out_sel(&mut self) -> PERI_OUT_SEL_W<'_, OUT_PERI_SEL_SPEC> {
        PERI_OUT_SEL_W::new(self, 0)
    }
}
#[doc = "Peripheral selection of Tx channel 0\n\nYou can [`read`](crate::Reg::read) this register and get [`out_peri_sel::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`out_peri_sel::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct OUT_PERI_SEL_SPEC;
impl crate::RegisterSpec for OUT_PERI_SEL_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`out_peri_sel::R`](R) reader structure"]
impl crate::Readable for OUT_PERI_SEL_SPEC {}
#[doc = "`write(|w| ..)` method takes [`out_peri_sel::W`](W) writer structure"]
impl crate::Writable for OUT_PERI_SEL_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets OUT_PERI_SEL to value 0x3f"]
impl crate::Resettable for OUT_PERI_SEL_SPEC {
    const RESET_VALUE: u32 = 0x3f;
}
