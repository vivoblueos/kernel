#[doc = "Register `SADDR1` reader"]
pub type R = crate::R<Saddr1Spec>;
#[doc = "Register `SADDR1` writer"]
pub type W = crate::W<Saddr1Spec>;
#[doc = "Field `ADDRESS2` reader - Second I2C address for the slave"]
pub type Address2R = crate::FieldReader;
#[doc = "Field `ADDRESS2` writer - Second I2C address for the slave"]
pub type Address2W<'a, REG> = crate::FieldWriter<'a, REG, 7>;
#[doc = "Field `ADDMSK2` reader - ADDRESS2\\[7:1\\]
mask"]
pub type Addmsk2R = crate::FieldReader;
#[doc = "Field `ADDMSK2` writer - ADDRESS2\\[7:1\\]
mask"]
pub type Addmsk2W<'a, REG> = crate::FieldWriter<'a, REG, 3>;
#[doc = "Field `ADDRESS2EN` reader - Second I2C address enable"]
pub type Address2enR = crate::BitReader;
#[doc = "Field `ADDRESS2EN` writer - Second I2C address enable"]
pub type Address2enW<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bits 1:7 - Second I2C address for the slave"]
    #[inline(always)]
    pub fn address2(&self) -> Address2R {
        Address2R::new(((self.bits >> 1) & 0x7f) as u8)
    }
    #[doc = "Bits 8:10 - ADDRESS2\\[7:1\\]
mask"]
    #[inline(always)]
    pub fn addmsk2(&self) -> Addmsk2R {
        Addmsk2R::new(((self.bits >> 8) & 7) as u8)
    }
    #[doc = "Bit 15 - Second I2C address enable"]
    #[inline(always)]
    pub fn address2en(&self) -> Address2enR {
        Address2enR::new(((self.bits >> 15) & 1) != 0)
    }
}
impl W {
    #[doc = "Bits 1:7 - Second I2C address for the slave"]
    #[inline(always)]
    #[must_use]
    pub fn address2(&mut self) -> Address2W<Saddr1Spec> {
        Address2W::new(self, 1)
    }
    #[doc = "Bits 8:10 - ADDRESS2\\[7:1\\]
mask"]
    #[inline(always)]
    #[must_use]
    pub fn addmsk2(&mut self) -> Addmsk2W<Saddr1Spec> {
        Addmsk2W::new(self, 8)
    }
    #[doc = "Bit 15 - Second I2C address enable"]
    #[inline(always)]
    #[must_use]
    pub fn address2en(&mut self) -> Address2enW<Saddr1Spec> {
        Address2enW::new(self, 15)
    }
}
#[doc = "Slave address register 1\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`saddr1::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`saddr1::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct Saddr1Spec;
impl crate::RegisterSpec for Saddr1Spec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`saddr1::R`](R) reader structure"]
impl crate::Readable for Saddr1Spec {}
#[doc = "`write(|w| ..)` method takes [`saddr1::W`](W) writer structure"]
impl crate::Writable for Saddr1Spec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets SADDR1 to value 0"]
impl crate::Resettable for Saddr1Spec {
    const RESET_VALUE: u32 = 0;
}
