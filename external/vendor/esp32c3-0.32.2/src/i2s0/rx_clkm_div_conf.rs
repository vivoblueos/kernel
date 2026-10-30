#[doc = "Register `RX_CLKM_DIV_CONF` reader"]
pub type R = crate::R<RX_CLKM_DIV_CONF_SPEC>;
#[doc = "Register `RX_CLKM_DIV_CONF` writer"]
pub type W = crate::W<RX_CLKM_DIV_CONF_SPEC>;
#[doc = "Field `RX_CLKM_DIV_Z` reader - For b <= a/2, the value of I2S_RX_CLKM_DIV_Z is b. For b > a/2, the value of I2S_RX_CLKM_DIV_Z is (a-b)."]
pub type RX_CLKM_DIV_Z_R = crate::FieldReader<u16>;
#[doc = "Field `RX_CLKM_DIV_Z` writer - For b <= a/2, the value of I2S_RX_CLKM_DIV_Z is b. For b > a/2, the value of I2S_RX_CLKM_DIV_Z is (a-b)."]
pub type RX_CLKM_DIV_Z_W<'a, REG> = crate::FieldWriter<'a, REG, 9, u16>;
#[doc = "Field `RX_CLKM_DIV_Y` reader - For b <= a/2, the value of I2S_RX_CLKM_DIV_Y is (a%b) . For b > a/2, the value of I2S_RX_CLKM_DIV_Y is (a%(a-b))."]
pub type RX_CLKM_DIV_Y_R = crate::FieldReader<u16>;
#[doc = "Field `RX_CLKM_DIV_Y` writer - For b <= a/2, the value of I2S_RX_CLKM_DIV_Y is (a%b) . For b > a/2, the value of I2S_RX_CLKM_DIV_Y is (a%(a-b))."]
pub type RX_CLKM_DIV_Y_W<'a, REG> = crate::FieldWriter<'a, REG, 9, u16>;
#[doc = "Field `RX_CLKM_DIV_X` reader - For b <= a/2, the value of I2S_RX_CLKM_DIV_X is (a/b) - 1. For b > a/2, the value of I2S_RX_CLKM_DIV_X is (a/(a-b)) - 1."]
pub type RX_CLKM_DIV_X_R = crate::FieldReader<u16>;
#[doc = "Field `RX_CLKM_DIV_X` writer - For b <= a/2, the value of I2S_RX_CLKM_DIV_X is (a/b) - 1. For b > a/2, the value of I2S_RX_CLKM_DIV_X is (a/(a-b)) - 1."]
pub type RX_CLKM_DIV_X_W<'a, REG> = crate::FieldWriter<'a, REG, 9, u16>;
#[doc = "Field `RX_CLKM_DIV_YN1` reader - For b <= a/2, the value of I2S_RX_CLKM_DIV_YN1 is 0 . For b > a/2, the value of I2S_RX_CLKM_DIV_YN1 is 1."]
pub type RX_CLKM_DIV_YN1_R = crate::BitReader;
#[doc = "Field `RX_CLKM_DIV_YN1` writer - For b <= a/2, the value of I2S_RX_CLKM_DIV_YN1 is 0 . For b > a/2, the value of I2S_RX_CLKM_DIV_YN1 is 1."]
pub type RX_CLKM_DIV_YN1_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bits 0:8 - For b <= a/2, the value of I2S_RX_CLKM_DIV_Z is b. For b > a/2, the value of I2S_RX_CLKM_DIV_Z is (a-b)."]
    #[inline(always)]
    pub fn rx_clkm_div_z(&self) -> RX_CLKM_DIV_Z_R {
        RX_CLKM_DIV_Z_R::new((self.bits & 0x01ff) as u16)
    }
    #[doc = "Bits 9:17 - For b <= a/2, the value of I2S_RX_CLKM_DIV_Y is (a%b) . For b > a/2, the value of I2S_RX_CLKM_DIV_Y is (a%(a-b))."]
    #[inline(always)]
    pub fn rx_clkm_div_y(&self) -> RX_CLKM_DIV_Y_R {
        RX_CLKM_DIV_Y_R::new(((self.bits >> 9) & 0x01ff) as u16)
    }
    #[doc = "Bits 18:26 - For b <= a/2, the value of I2S_RX_CLKM_DIV_X is (a/b) - 1. For b > a/2, the value of I2S_RX_CLKM_DIV_X is (a/(a-b)) - 1."]
    #[inline(always)]
    pub fn rx_clkm_div_x(&self) -> RX_CLKM_DIV_X_R {
        RX_CLKM_DIV_X_R::new(((self.bits >> 18) & 0x01ff) as u16)
    }
    #[doc = "Bit 27 - For b <= a/2, the value of I2S_RX_CLKM_DIV_YN1 is 0 . For b > a/2, the value of I2S_RX_CLKM_DIV_YN1 is 1."]
    #[inline(always)]
    pub fn rx_clkm_div_yn1(&self) -> RX_CLKM_DIV_YN1_R {
        RX_CLKM_DIV_YN1_R::new(((self.bits >> 27) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("RX_CLKM_DIV_CONF")
            .field("rx_clkm_div_z", &self.rx_clkm_div_z())
            .field("rx_clkm_div_y", &self.rx_clkm_div_y())
            .field("rx_clkm_div_x", &self.rx_clkm_div_x())
            .field("rx_clkm_div_yn1", &self.rx_clkm_div_yn1())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:8 - For b <= a/2, the value of I2S_RX_CLKM_DIV_Z is b. For b > a/2, the value of I2S_RX_CLKM_DIV_Z is (a-b)."]
    #[inline(always)]
    pub fn rx_clkm_div_z(&mut self) -> RX_CLKM_DIV_Z_W<'_, RX_CLKM_DIV_CONF_SPEC> {
        RX_CLKM_DIV_Z_W::new(self, 0)
    }
    #[doc = "Bits 9:17 - For b <= a/2, the value of I2S_RX_CLKM_DIV_Y is (a%b) . For b > a/2, the value of I2S_RX_CLKM_DIV_Y is (a%(a-b))."]
    #[inline(always)]
    pub fn rx_clkm_div_y(&mut self) -> RX_CLKM_DIV_Y_W<'_, RX_CLKM_DIV_CONF_SPEC> {
        RX_CLKM_DIV_Y_W::new(self, 9)
    }
    #[doc = "Bits 18:26 - For b <= a/2, the value of I2S_RX_CLKM_DIV_X is (a/b) - 1. For b > a/2, the value of I2S_RX_CLKM_DIV_X is (a/(a-b)) - 1."]
    #[inline(always)]
    pub fn rx_clkm_div_x(&mut self) -> RX_CLKM_DIV_X_W<'_, RX_CLKM_DIV_CONF_SPEC> {
        RX_CLKM_DIV_X_W::new(self, 18)
    }
    #[doc = "Bit 27 - For b <= a/2, the value of I2S_RX_CLKM_DIV_YN1 is 0 . For b > a/2, the value of I2S_RX_CLKM_DIV_YN1 is 1."]
    #[inline(always)]
    pub fn rx_clkm_div_yn1(&mut self) -> RX_CLKM_DIV_YN1_W<'_, RX_CLKM_DIV_CONF_SPEC> {
        RX_CLKM_DIV_YN1_W::new(self, 27)
    }
}
#[doc = "I2S RX module clock divider configure register\n\nYou can [`read`](crate::Reg::read) this register and get [`rx_clkm_div_conf::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`rx_clkm_div_conf::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct RX_CLKM_DIV_CONF_SPEC;
impl crate::RegisterSpec for RX_CLKM_DIV_CONF_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`rx_clkm_div_conf::R`](R) reader structure"]
impl crate::Readable for RX_CLKM_DIV_CONF_SPEC {}
#[doc = "`write(|w| ..)` method takes [`rx_clkm_div_conf::W`](W) writer structure"]
impl crate::Writable for RX_CLKM_DIV_CONF_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets RX_CLKM_DIV_CONF to value 0x0200"]
impl crate::Resettable for RX_CLKM_DIV_CONF_SPEC {
    const RESET_VALUE: u32 = 0x0200;
}
