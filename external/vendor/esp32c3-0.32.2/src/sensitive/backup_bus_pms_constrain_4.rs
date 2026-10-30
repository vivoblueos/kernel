#[doc = "Register `BACKUP_BUS_PMS_CONSTRAIN_4` reader"]
pub type R = crate::R<BACKUP_BUS_PMS_CONSTRAIN_4_SPEC>;
#[doc = "Register `BACKUP_BUS_PMS_CONSTRAIN_4` writer"]
pub type W = crate::W<BACKUP_BUS_PMS_CONSTRAIN_4_SPEC>;
#[doc = "Field `BACKUP_BUS_PMS_CONSTRAIN_USB_WRAP` reader - backup_bus_pms_constrain_usb_wrap"]
pub type BACKUP_BUS_PMS_CONSTRAIN_USB_WRAP_R = crate::FieldReader;
#[doc = "Field `BACKUP_BUS_PMS_CONSTRAIN_USB_WRAP` writer - backup_bus_pms_constrain_usb_wrap"]
pub type BACKUP_BUS_PMS_CONSTRAIN_USB_WRAP_W<'a, REG> = crate::FieldWriter<'a, REG, 2>;
#[doc = "Field `BACKUP_BUS_PMS_CONSTRAIN_CRYPTO_PERI` reader - backup_bus_pms_constrain_crypto_peri"]
pub type BACKUP_BUS_PMS_CONSTRAIN_CRYPTO_PERI_R = crate::FieldReader;
#[doc = "Field `BACKUP_BUS_PMS_CONSTRAIN_CRYPTO_PERI` writer - backup_bus_pms_constrain_crypto_peri"]
pub type BACKUP_BUS_PMS_CONSTRAIN_CRYPTO_PERI_W<'a, REG> = crate::FieldWriter<'a, REG, 2>;
#[doc = "Field `BACKUP_BUS_PMS_CONSTRAIN_CRYPTO_DMA` reader - backup_bus_pms_constrain_crypto_dma"]
pub type BACKUP_BUS_PMS_CONSTRAIN_CRYPTO_DMA_R = crate::FieldReader;
#[doc = "Field `BACKUP_BUS_PMS_CONSTRAIN_CRYPTO_DMA` writer - backup_bus_pms_constrain_crypto_dma"]
pub type BACKUP_BUS_PMS_CONSTRAIN_CRYPTO_DMA_W<'a, REG> = crate::FieldWriter<'a, REG, 2>;
#[doc = "Field `BACKUP_BUS_PMS_CONSTRAIN_APB_ADC` reader - backup_bus_pms_constrain_apb_adc"]
pub type BACKUP_BUS_PMS_CONSTRAIN_APB_ADC_R = crate::FieldReader;
#[doc = "Field `BACKUP_BUS_PMS_CONSTRAIN_APB_ADC` writer - backup_bus_pms_constrain_apb_adc"]
pub type BACKUP_BUS_PMS_CONSTRAIN_APB_ADC_W<'a, REG> = crate::FieldWriter<'a, REG, 2>;
#[doc = "Field `BACKUP_BUS_PMS_CONSTRAIN_BT_PWR` reader - backup_bus_pms_constrain_bt_pwr"]
pub type BACKUP_BUS_PMS_CONSTRAIN_BT_PWR_R = crate::FieldReader;
#[doc = "Field `BACKUP_BUS_PMS_CONSTRAIN_BT_PWR` writer - backup_bus_pms_constrain_bt_pwr"]
pub type BACKUP_BUS_PMS_CONSTRAIN_BT_PWR_W<'a, REG> = crate::FieldWriter<'a, REG, 2>;
#[doc = "Field `BACKUP_BUS_PMS_CONSTRAIN_USB_DEVICE` reader - backup_bus_pms_constrain_usb_device"]
pub type BACKUP_BUS_PMS_CONSTRAIN_USB_DEVICE_R = crate::FieldReader;
#[doc = "Field `BACKUP_BUS_PMS_CONSTRAIN_USB_DEVICE` writer - backup_bus_pms_constrain_usb_device"]
pub type BACKUP_BUS_PMS_CONSTRAIN_USB_DEVICE_W<'a, REG> = crate::FieldWriter<'a, REG, 2>;
impl R {
    #[doc = "Bits 2:3 - backup_bus_pms_constrain_usb_wrap"]
    #[inline(always)]
    pub fn backup_bus_pms_constrain_usb_wrap(&self) -> BACKUP_BUS_PMS_CONSTRAIN_USB_WRAP_R {
        BACKUP_BUS_PMS_CONSTRAIN_USB_WRAP_R::new(((self.bits >> 2) & 3) as u8)
    }
    #[doc = "Bits 4:5 - backup_bus_pms_constrain_crypto_peri"]
    #[inline(always)]
    pub fn backup_bus_pms_constrain_crypto_peri(&self) -> BACKUP_BUS_PMS_CONSTRAIN_CRYPTO_PERI_R {
        BACKUP_BUS_PMS_CONSTRAIN_CRYPTO_PERI_R::new(((self.bits >> 4) & 3) as u8)
    }
    #[doc = "Bits 6:7 - backup_bus_pms_constrain_crypto_dma"]
    #[inline(always)]
    pub fn backup_bus_pms_constrain_crypto_dma(&self) -> BACKUP_BUS_PMS_CONSTRAIN_CRYPTO_DMA_R {
        BACKUP_BUS_PMS_CONSTRAIN_CRYPTO_DMA_R::new(((self.bits >> 6) & 3) as u8)
    }
    #[doc = "Bits 8:9 - backup_bus_pms_constrain_apb_adc"]
    #[inline(always)]
    pub fn backup_bus_pms_constrain_apb_adc(&self) -> BACKUP_BUS_PMS_CONSTRAIN_APB_ADC_R {
        BACKUP_BUS_PMS_CONSTRAIN_APB_ADC_R::new(((self.bits >> 8) & 3) as u8)
    }
    #[doc = "Bits 12:13 - backup_bus_pms_constrain_bt_pwr"]
    #[inline(always)]
    pub fn backup_bus_pms_constrain_bt_pwr(&self) -> BACKUP_BUS_PMS_CONSTRAIN_BT_PWR_R {
        BACKUP_BUS_PMS_CONSTRAIN_BT_PWR_R::new(((self.bits >> 12) & 3) as u8)
    }
    #[doc = "Bits 14:15 - backup_bus_pms_constrain_usb_device"]
    #[inline(always)]
    pub fn backup_bus_pms_constrain_usb_device(&self) -> BACKUP_BUS_PMS_CONSTRAIN_USB_DEVICE_R {
        BACKUP_BUS_PMS_CONSTRAIN_USB_DEVICE_R::new(((self.bits >> 14) & 3) as u8)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("BACKUP_BUS_PMS_CONSTRAIN_4")
            .field(
                "backup_bus_pms_constrain_usb_wrap",
                &self.backup_bus_pms_constrain_usb_wrap(),
            )
            .field(
                "backup_bus_pms_constrain_crypto_peri",
                &self.backup_bus_pms_constrain_crypto_peri(),
            )
            .field(
                "backup_bus_pms_constrain_crypto_dma",
                &self.backup_bus_pms_constrain_crypto_dma(),
            )
            .field(
                "backup_bus_pms_constrain_apb_adc",
                &self.backup_bus_pms_constrain_apb_adc(),
            )
            .field(
                "backup_bus_pms_constrain_bt_pwr",
                &self.backup_bus_pms_constrain_bt_pwr(),
            )
            .field(
                "backup_bus_pms_constrain_usb_device",
                &self.backup_bus_pms_constrain_usb_device(),
            )
            .finish()
    }
}
impl W {
    #[doc = "Bits 2:3 - backup_bus_pms_constrain_usb_wrap"]
    #[inline(always)]
    pub fn backup_bus_pms_constrain_usb_wrap(
        &mut self,
    ) -> BACKUP_BUS_PMS_CONSTRAIN_USB_WRAP_W<'_, BACKUP_BUS_PMS_CONSTRAIN_4_SPEC> {
        BACKUP_BUS_PMS_CONSTRAIN_USB_WRAP_W::new(self, 2)
    }
    #[doc = "Bits 4:5 - backup_bus_pms_constrain_crypto_peri"]
    #[inline(always)]
    pub fn backup_bus_pms_constrain_crypto_peri(
        &mut self,
    ) -> BACKUP_BUS_PMS_CONSTRAIN_CRYPTO_PERI_W<'_, BACKUP_BUS_PMS_CONSTRAIN_4_SPEC> {
        BACKUP_BUS_PMS_CONSTRAIN_CRYPTO_PERI_W::new(self, 4)
    }
    #[doc = "Bits 6:7 - backup_bus_pms_constrain_crypto_dma"]
    #[inline(always)]
    pub fn backup_bus_pms_constrain_crypto_dma(
        &mut self,
    ) -> BACKUP_BUS_PMS_CONSTRAIN_CRYPTO_DMA_W<'_, BACKUP_BUS_PMS_CONSTRAIN_4_SPEC> {
        BACKUP_BUS_PMS_CONSTRAIN_CRYPTO_DMA_W::new(self, 6)
    }
    #[doc = "Bits 8:9 - backup_bus_pms_constrain_apb_adc"]
    #[inline(always)]
    pub fn backup_bus_pms_constrain_apb_adc(
        &mut self,
    ) -> BACKUP_BUS_PMS_CONSTRAIN_APB_ADC_W<'_, BACKUP_BUS_PMS_CONSTRAIN_4_SPEC> {
        BACKUP_BUS_PMS_CONSTRAIN_APB_ADC_W::new(self, 8)
    }
    #[doc = "Bits 12:13 - backup_bus_pms_constrain_bt_pwr"]
    #[inline(always)]
    pub fn backup_bus_pms_constrain_bt_pwr(
        &mut self,
    ) -> BACKUP_BUS_PMS_CONSTRAIN_BT_PWR_W<'_, BACKUP_BUS_PMS_CONSTRAIN_4_SPEC> {
        BACKUP_BUS_PMS_CONSTRAIN_BT_PWR_W::new(self, 12)
    }
    #[doc = "Bits 14:15 - backup_bus_pms_constrain_usb_device"]
    #[inline(always)]
    pub fn backup_bus_pms_constrain_usb_device(
        &mut self,
    ) -> BACKUP_BUS_PMS_CONSTRAIN_USB_DEVICE_W<'_, BACKUP_BUS_PMS_CONSTRAIN_4_SPEC> {
        BACKUP_BUS_PMS_CONSTRAIN_USB_DEVICE_W::new(self, 14)
    }
}
#[doc = "SENSITIVE_BACKUP_BUS_PMS_CONSTRAIN_4_REG\n\nYou can [`read`](crate::Reg::read) this register and get [`backup_bus_pms_constrain_4::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`backup_bus_pms_constrain_4::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct BACKUP_BUS_PMS_CONSTRAIN_4_SPEC;
impl crate::RegisterSpec for BACKUP_BUS_PMS_CONSTRAIN_4_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`backup_bus_pms_constrain_4::R`](R) reader structure"]
impl crate::Readable for BACKUP_BUS_PMS_CONSTRAIN_4_SPEC {}
#[doc = "`write(|w| ..)` method takes [`backup_bus_pms_constrain_4::W`](W) writer structure"]
impl crate::Writable for BACKUP_BUS_PMS_CONSTRAIN_4_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets BACKUP_BUS_PMS_CONSTRAIN_4 to value 0xf3fc"]
impl crate::Resettable for BACKUP_BUS_PMS_CONSTRAIN_4_SPEC {
    const RESET_VALUE: u32 = 0xf3fc;
}
