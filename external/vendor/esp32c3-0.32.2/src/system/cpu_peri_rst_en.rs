#[doc = "Register `CPU_PERI_RST_EN` reader"]
pub type R = crate::R<CPU_PERI_RST_EN_SPEC>;
#[doc = "Register `CPU_PERI_RST_EN` writer"]
pub type W = crate::W<CPU_PERI_RST_EN_SPEC>;
#[doc = "Field `RST_EN_ASSIST_DEBUG` reader - reg_rst_en_assist_debug"]
pub type RST_EN_ASSIST_DEBUG_R = crate::BitReader;
#[doc = "Field `RST_EN_ASSIST_DEBUG` writer - reg_rst_en_assist_debug"]
pub type RST_EN_ASSIST_DEBUG_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `RST_EN_DEDICATED_GPIO` reader - reg_rst_en_dedicated_gpio"]
pub type RST_EN_DEDICATED_GPIO_R = crate::BitReader;
#[doc = "Field `RST_EN_DEDICATED_GPIO` writer - reg_rst_en_dedicated_gpio"]
pub type RST_EN_DEDICATED_GPIO_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 6 - reg_rst_en_assist_debug"]
    #[inline(always)]
    pub fn rst_en_assist_debug(&self) -> RST_EN_ASSIST_DEBUG_R {
        RST_EN_ASSIST_DEBUG_R::new(((self.bits >> 6) & 1) != 0)
    }
    #[doc = "Bit 7 - reg_rst_en_dedicated_gpio"]
    #[inline(always)]
    pub fn rst_en_dedicated_gpio(&self) -> RST_EN_DEDICATED_GPIO_R {
        RST_EN_DEDICATED_GPIO_R::new(((self.bits >> 7) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("CPU_PERI_RST_EN")
            .field("rst_en_assist_debug", &self.rst_en_assist_debug())
            .field("rst_en_dedicated_gpio", &self.rst_en_dedicated_gpio())
            .finish()
    }
}
impl W {
    #[doc = "Bit 6 - reg_rst_en_assist_debug"]
    #[inline(always)]
    pub fn rst_en_assist_debug(&mut self) -> RST_EN_ASSIST_DEBUG_W<'_, CPU_PERI_RST_EN_SPEC> {
        RST_EN_ASSIST_DEBUG_W::new(self, 6)
    }
    #[doc = "Bit 7 - reg_rst_en_dedicated_gpio"]
    #[inline(always)]
    pub fn rst_en_dedicated_gpio(&mut self) -> RST_EN_DEDICATED_GPIO_W<'_, CPU_PERI_RST_EN_SPEC> {
        RST_EN_DEDICATED_GPIO_W::new(self, 7)
    }
}
#[doc = "cpu_peripheral reset register\n\nYou can [`read`](crate::Reg::read) this register and get [`cpu_peri_rst_en::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`cpu_peri_rst_en::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct CPU_PERI_RST_EN_SPEC;
impl crate::RegisterSpec for CPU_PERI_RST_EN_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`cpu_peri_rst_en::R`](R) reader structure"]
impl crate::Readable for CPU_PERI_RST_EN_SPEC {}
#[doc = "`write(|w| ..)` method takes [`cpu_peri_rst_en::W`](W) writer structure"]
impl crate::Writable for CPU_PERI_RST_EN_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets CPU_PERI_RST_EN to value 0xc0"]
impl crate::Resettable for CPU_PERI_RST_EN_SPEC {
    const RESET_VALUE: u32 = 0xc0;
}
