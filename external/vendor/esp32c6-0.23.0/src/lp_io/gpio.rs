#[doc = "Register `GPIO%s` reader"]
pub type R = crate::R<GPIO_SPEC>;
#[doc = "Register `GPIO%s` writer"]
pub type W = crate::W<GPIO_SPEC>;
#[doc = "Field `MCU_OE` reader - need des"]
pub type MCU_OE_R = crate::BitReader;
#[doc = "Field `MCU_OE` writer - need des"]
pub type MCU_OE_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SLP_SEL` reader - need des"]
pub type SLP_SEL_R = crate::BitReader;
#[doc = "Field `SLP_SEL` writer - need des"]
pub type SLP_SEL_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `MCU_WPD` reader - need des"]
pub type MCU_WPD_R = crate::BitReader;
#[doc = "Field `MCU_WPD` writer - need des"]
pub type MCU_WPD_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `MCU_WPU` reader - need des"]
pub type MCU_WPU_R = crate::BitReader;
#[doc = "Field `MCU_WPU` writer - need des"]
pub type MCU_WPU_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `MCU_IE` reader - need des"]
pub type MCU_IE_R = crate::BitReader;
#[doc = "Field `MCU_IE` writer - need des"]
pub type MCU_IE_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `MCU_DRV` reader - need des"]
pub type MCU_DRV_R = crate::FieldReader;
#[doc = "Field `MCU_DRV` writer - need des"]
pub type MCU_DRV_W<'a, REG> = crate::FieldWriter<'a, REG, 2>;
#[doc = "Field `FUN_WPD` reader - need des"]
pub type FUN_WPD_R = crate::BitReader;
#[doc = "Field `FUN_WPD` writer - need des"]
pub type FUN_WPD_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `FUN_WPU` reader - need des"]
pub type FUN_WPU_R = crate::BitReader;
#[doc = "Field `FUN_WPU` writer - need des"]
pub type FUN_WPU_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `FUN_IE` reader - need des"]
pub type FUN_IE_R = crate::BitReader;
#[doc = "Field `FUN_IE` writer - need des"]
pub type FUN_IE_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `FUN_DRV` reader - need des"]
pub type FUN_DRV_R = crate::FieldReader;
#[doc = "Field `FUN_DRV` writer - need des"]
pub type FUN_DRV_W<'a, REG> = crate::FieldWriter<'a, REG, 2>;
#[doc = "Field `MCU_SEL` reader - need des"]
pub type MCU_SEL_R = crate::FieldReader;
#[doc = "Field `MCU_SEL` writer - need des"]
pub type MCU_SEL_W<'a, REG> = crate::FieldWriter<'a, REG, 3>;
impl R {
    #[doc = "Bit 0 - need des"]
    #[inline(always)]
    pub fn mcu_oe(&self) -> MCU_OE_R {
        MCU_OE_R::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - need des"]
    #[inline(always)]
    pub fn slp_sel(&self) -> SLP_SEL_R {
        SLP_SEL_R::new(((self.bits >> 1) & 1) != 0)
    }
    #[doc = "Bit 2 - need des"]
    #[inline(always)]
    pub fn mcu_wpd(&self) -> MCU_WPD_R {
        MCU_WPD_R::new(((self.bits >> 2) & 1) != 0)
    }
    #[doc = "Bit 3 - need des"]
    #[inline(always)]
    pub fn mcu_wpu(&self) -> MCU_WPU_R {
        MCU_WPU_R::new(((self.bits >> 3) & 1) != 0)
    }
    #[doc = "Bit 4 - need des"]
    #[inline(always)]
    pub fn mcu_ie(&self) -> MCU_IE_R {
        MCU_IE_R::new(((self.bits >> 4) & 1) != 0)
    }
    #[doc = "Bits 5:6 - need des"]
    #[inline(always)]
    pub fn mcu_drv(&self) -> MCU_DRV_R {
        MCU_DRV_R::new(((self.bits >> 5) & 3) as u8)
    }
    #[doc = "Bit 7 - need des"]
    #[inline(always)]
    pub fn fun_wpd(&self) -> FUN_WPD_R {
        FUN_WPD_R::new(((self.bits >> 7) & 1) != 0)
    }
    #[doc = "Bit 8 - need des"]
    #[inline(always)]
    pub fn fun_wpu(&self) -> FUN_WPU_R {
        FUN_WPU_R::new(((self.bits >> 8) & 1) != 0)
    }
    #[doc = "Bit 9 - need des"]
    #[inline(always)]
    pub fn fun_ie(&self) -> FUN_IE_R {
        FUN_IE_R::new(((self.bits >> 9) & 1) != 0)
    }
    #[doc = "Bits 10:11 - need des"]
    #[inline(always)]
    pub fn fun_drv(&self) -> FUN_DRV_R {
        FUN_DRV_R::new(((self.bits >> 10) & 3) as u8)
    }
    #[doc = "Bits 12:14 - need des"]
    #[inline(always)]
    pub fn mcu_sel(&self) -> MCU_SEL_R {
        MCU_SEL_R::new(((self.bits >> 12) & 7) as u8)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("GPIO")
            .field("mcu_oe", &self.mcu_oe())
            .field("slp_sel", &self.slp_sel())
            .field("mcu_wpd", &self.mcu_wpd())
            .field("mcu_wpu", &self.mcu_wpu())
            .field("mcu_ie", &self.mcu_ie())
            .field("mcu_drv", &self.mcu_drv())
            .field("fun_wpd", &self.fun_wpd())
            .field("fun_wpu", &self.fun_wpu())
            .field("fun_ie", &self.fun_ie())
            .field("fun_drv", &self.fun_drv())
            .field("mcu_sel", &self.mcu_sel())
            .finish()
    }
}
impl W {
    #[doc = "Bit 0 - need des"]
    #[inline(always)]
    pub fn mcu_oe(&mut self) -> MCU_OE_W<'_, GPIO_SPEC> {
        MCU_OE_W::new(self, 0)
    }
    #[doc = "Bit 1 - need des"]
    #[inline(always)]
    pub fn slp_sel(&mut self) -> SLP_SEL_W<'_, GPIO_SPEC> {
        SLP_SEL_W::new(self, 1)
    }
    #[doc = "Bit 2 - need des"]
    #[inline(always)]
    pub fn mcu_wpd(&mut self) -> MCU_WPD_W<'_, GPIO_SPEC> {
        MCU_WPD_W::new(self, 2)
    }
    #[doc = "Bit 3 - need des"]
    #[inline(always)]
    pub fn mcu_wpu(&mut self) -> MCU_WPU_W<'_, GPIO_SPEC> {
        MCU_WPU_W::new(self, 3)
    }
    #[doc = "Bit 4 - need des"]
    #[inline(always)]
    pub fn mcu_ie(&mut self) -> MCU_IE_W<'_, GPIO_SPEC> {
        MCU_IE_W::new(self, 4)
    }
    #[doc = "Bits 5:6 - need des"]
    #[inline(always)]
    pub fn mcu_drv(&mut self) -> MCU_DRV_W<'_, GPIO_SPEC> {
        MCU_DRV_W::new(self, 5)
    }
    #[doc = "Bit 7 - need des"]
    #[inline(always)]
    pub fn fun_wpd(&mut self) -> FUN_WPD_W<'_, GPIO_SPEC> {
        FUN_WPD_W::new(self, 7)
    }
    #[doc = "Bit 8 - need des"]
    #[inline(always)]
    pub fn fun_wpu(&mut self) -> FUN_WPU_W<'_, GPIO_SPEC> {
        FUN_WPU_W::new(self, 8)
    }
    #[doc = "Bit 9 - need des"]
    #[inline(always)]
    pub fn fun_ie(&mut self) -> FUN_IE_W<'_, GPIO_SPEC> {
        FUN_IE_W::new(self, 9)
    }
    #[doc = "Bits 10:11 - need des"]
    #[inline(always)]
    pub fn fun_drv(&mut self) -> FUN_DRV_W<'_, GPIO_SPEC> {
        FUN_DRV_W::new(self, 10)
    }
    #[doc = "Bits 12:14 - need des"]
    #[inline(always)]
    pub fn mcu_sel(&mut self) -> MCU_SEL_W<'_, GPIO_SPEC> {
        MCU_SEL_W::new(self, 12)
    }
}
#[doc = "need des\n\nYou can [`read`](crate::Reg::read) this register and get [`gpio::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`gpio::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct GPIO_SPEC;
impl crate::RegisterSpec for GPIO_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`gpio::R`](R) reader structure"]
impl crate::Readable for GPIO_SPEC {}
#[doc = "`write(|w| ..)` method takes [`gpio::W`](W) writer structure"]
impl crate::Writable for GPIO_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets GPIO%s to value 0"]
impl crate::Resettable for GPIO_SPEC {}
