#[doc = "Register `SARADC_CLKM_CONF` reader"]
pub type R = crate::R<SARADC_CLKM_CONF_SPEC>;
#[doc = "Register `SARADC_CLKM_CONF` writer"]
pub type W = crate::W<SARADC_CLKM_CONF_SPEC>;
#[doc = "Field `SARADC_CLKM_DIV_A` reader - The denominator of the frequency divider factor of the saradc function clock."]
pub type SARADC_CLKM_DIV_A_R = crate::FieldReader;
#[doc = "Field `SARADC_CLKM_DIV_A` writer - The denominator of the frequency divider factor of the saradc function clock."]
pub type SARADC_CLKM_DIV_A_W<'a, REG> = crate::FieldWriter<'a, REG, 6>;
#[doc = "Field `SARADC_CLKM_DIV_B` reader - The numerator of the frequency divider factor of the saradc function clock."]
pub type SARADC_CLKM_DIV_B_R = crate::FieldReader;
#[doc = "Field `SARADC_CLKM_DIV_B` writer - The numerator of the frequency divider factor of the saradc function clock."]
pub type SARADC_CLKM_DIV_B_W<'a, REG> = crate::FieldWriter<'a, REG, 6>;
#[doc = "Field `SARADC_CLKM_DIV_NUM` reader - The integral part of the frequency divider factor of the saradc function clock."]
pub type SARADC_CLKM_DIV_NUM_R = crate::FieldReader;
#[doc = "Field `SARADC_CLKM_DIV_NUM` writer - The integral part of the frequency divider factor of the saradc function clock."]
pub type SARADC_CLKM_DIV_NUM_W<'a, REG> = crate::FieldWriter<'a, REG, 8>;
#[doc = "Field `SARADC_CLKM_SEL` reader - set this field to select clock-source. 0(default): XTAL, 1: 240MHz, 2: FOSC, 3: reserved."]
pub type SARADC_CLKM_SEL_R = crate::FieldReader;
#[doc = "Field `SARADC_CLKM_SEL` writer - set this field to select clock-source. 0(default): XTAL, 1: 240MHz, 2: FOSC, 3: reserved."]
pub type SARADC_CLKM_SEL_W<'a, REG> = crate::FieldWriter<'a, REG, 2>;
#[doc = "Field `SARADC_CLKM_EN` reader - Set 1 to enable saradc function clock"]
pub type SARADC_CLKM_EN_R = crate::BitReader;
#[doc = "Field `SARADC_CLKM_EN` writer - Set 1 to enable saradc function clock"]
pub type SARADC_CLKM_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bits 0:5 - The denominator of the frequency divider factor of the saradc function clock."]
    #[inline(always)]
    pub fn saradc_clkm_div_a(&self) -> SARADC_CLKM_DIV_A_R {
        SARADC_CLKM_DIV_A_R::new((self.bits & 0x3f) as u8)
    }
    #[doc = "Bits 6:11 - The numerator of the frequency divider factor of the saradc function clock."]
    #[inline(always)]
    pub fn saradc_clkm_div_b(&self) -> SARADC_CLKM_DIV_B_R {
        SARADC_CLKM_DIV_B_R::new(((self.bits >> 6) & 0x3f) as u8)
    }
    #[doc = "Bits 12:19 - The integral part of the frequency divider factor of the saradc function clock."]
    #[inline(always)]
    pub fn saradc_clkm_div_num(&self) -> SARADC_CLKM_DIV_NUM_R {
        SARADC_CLKM_DIV_NUM_R::new(((self.bits >> 12) & 0xff) as u8)
    }
    #[doc = "Bits 20:21 - set this field to select clock-source. 0(default): XTAL, 1: 240MHz, 2: FOSC, 3: reserved."]
    #[inline(always)]
    pub fn saradc_clkm_sel(&self) -> SARADC_CLKM_SEL_R {
        SARADC_CLKM_SEL_R::new(((self.bits >> 20) & 3) as u8)
    }
    #[doc = "Bit 22 - Set 1 to enable saradc function clock"]
    #[inline(always)]
    pub fn saradc_clkm_en(&self) -> SARADC_CLKM_EN_R {
        SARADC_CLKM_EN_R::new(((self.bits >> 22) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("SARADC_CLKM_CONF")
            .field("saradc_clkm_div_a", &self.saradc_clkm_div_a())
            .field("saradc_clkm_div_b", &self.saradc_clkm_div_b())
            .field("saradc_clkm_div_num", &self.saradc_clkm_div_num())
            .field("saradc_clkm_sel", &self.saradc_clkm_sel())
            .field("saradc_clkm_en", &self.saradc_clkm_en())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:5 - The denominator of the frequency divider factor of the saradc function clock."]
    #[inline(always)]
    pub fn saradc_clkm_div_a(&mut self) -> SARADC_CLKM_DIV_A_W<'_, SARADC_CLKM_CONF_SPEC> {
        SARADC_CLKM_DIV_A_W::new(self, 0)
    }
    #[doc = "Bits 6:11 - The numerator of the frequency divider factor of the saradc function clock."]
    #[inline(always)]
    pub fn saradc_clkm_div_b(&mut self) -> SARADC_CLKM_DIV_B_W<'_, SARADC_CLKM_CONF_SPEC> {
        SARADC_CLKM_DIV_B_W::new(self, 6)
    }
    #[doc = "Bits 12:19 - The integral part of the frequency divider factor of the saradc function clock."]
    #[inline(always)]
    pub fn saradc_clkm_div_num(&mut self) -> SARADC_CLKM_DIV_NUM_W<'_, SARADC_CLKM_CONF_SPEC> {
        SARADC_CLKM_DIV_NUM_W::new(self, 12)
    }
    #[doc = "Bits 20:21 - set this field to select clock-source. 0(default): XTAL, 1: 240MHz, 2: FOSC, 3: reserved."]
    #[inline(always)]
    pub fn saradc_clkm_sel(&mut self) -> SARADC_CLKM_SEL_W<'_, SARADC_CLKM_CONF_SPEC> {
        SARADC_CLKM_SEL_W::new(self, 20)
    }
    #[doc = "Bit 22 - Set 1 to enable saradc function clock"]
    #[inline(always)]
    pub fn saradc_clkm_en(&mut self) -> SARADC_CLKM_EN_W<'_, SARADC_CLKM_CONF_SPEC> {
        SARADC_CLKM_EN_W::new(self, 22)
    }
}
#[doc = "SARADC_CLKM configuration register\n\nYou can [`read`](crate::Reg::read) this register and get [`saradc_clkm_conf::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`saradc_clkm_conf::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct SARADC_CLKM_CONF_SPEC;
impl crate::RegisterSpec for SARADC_CLKM_CONF_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`saradc_clkm_conf::R`](R) reader structure"]
impl crate::Readable for SARADC_CLKM_CONF_SPEC {}
#[doc = "`write(|w| ..)` method takes [`saradc_clkm_conf::W`](W) writer structure"]
impl crate::Writable for SARADC_CLKM_CONF_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets SARADC_CLKM_CONF to value 0x0040_4000"]
impl crate::Resettable for SARADC_CLKM_CONF_SPEC {
    const RESET_VALUE: u32 = 0x0040_4000;
}
