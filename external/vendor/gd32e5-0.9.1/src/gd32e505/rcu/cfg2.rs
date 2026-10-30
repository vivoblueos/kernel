#[doc = "Register `CFG2` reader"]
pub type R = crate::R<Cfg2Spec>;
#[doc = "Register `CFG2` writer"]
pub type W = crate::W<Cfg2Spec>;
#[doc = "Field `USART5SEL` reader - USART5 Clock Source Selection"]
pub type Usart5selR = crate::FieldReader;
#[doc = "Field `USART5SEL` writer - USART5 Clock Source Selection"]
pub type Usart5selW<'a, REG> = crate::FieldWriter<'a, REG, 2>;
#[doc = "Field `I2C2SEL` reader - I2C2 Clock Source Selection"]
pub type I2c2selR = crate::FieldReader;
#[doc = "Field `I2C2SEL` writer - I2C2 Clock Source Selection"]
pub type I2c2selW<'a, REG> = crate::FieldWriter<'a, REG, 2>;
impl R {
    #[doc = "Bits 0:1 - USART5 Clock Source Selection"]
    #[inline(always)]
    pub fn usart5sel(&self) -> Usart5selR {
        Usart5selR::new((self.bits & 3) as u8)
    }
    #[doc = "Bits 4:5 - I2C2 Clock Source Selection"]
    #[inline(always)]
    pub fn i2c2sel(&self) -> I2c2selR {
        I2c2selR::new(((self.bits >> 4) & 3) as u8)
    }
}
impl W {
    #[doc = "Bits 0:1 - USART5 Clock Source Selection"]
    #[inline(always)]
    #[must_use]
    pub fn usart5sel(&mut self) -> Usart5selW<Cfg2Spec> {
        Usart5selW::new(self, 0)
    }
    #[doc = "Bits 4:5 - I2C2 Clock Source Selection"]
    #[inline(always)]
    #[must_use]
    pub fn i2c2sel(&mut self) -> I2c2selW<Cfg2Spec> {
        I2c2selW::new(self, 4)
    }
}
#[doc = "Clock configuration register 2\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`cfg2::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`cfg2::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct Cfg2Spec;
impl crate::RegisterSpec for Cfg2Spec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`cfg2::R`](R) reader structure"]
impl crate::Readable for Cfg2Spec {}
#[doc = "`write(|w| ..)` method takes [`cfg2::W`](W) writer structure"]
impl crate::Writable for Cfg2Spec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets CFG2 to value 0"]
impl crate::Resettable for Cfg2Spec {
    const RESET_VALUE: u32 = 0;
}
