#[doc = "Register `SADDR0` reader"]
pub type R = crate::R<Saddr0Spec>;
#[doc = "Register `SADDR0` writer"]
pub type W = crate::W<Saddr0Spec>;
#[doc = "Field `ADDRESS_0` reader - Bit 0 of a 10-bit address"]
pub type Address0R = crate::BitReader;
#[doc = "Field `ADDRESS_0` writer - Bit 0 of a 10-bit address"]
pub type Address0W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ADDRESS_1_7` reader - Highest two bits of a 10-bit address"]
pub type Address1_7R = crate::FieldReader;
#[doc = "Field `ADDRESS_1_7` writer - Highest two bits of a 10-bit address"]
pub type Address1_7W<'a, REG> = crate::FieldWriter<'a, REG, 7>;
#[doc = "Field `ADDRESS_8_9` reader - 7-bit address or bits 7:1 of a 10-bit address"]
pub type Address8_9R = crate::FieldReader;
#[doc = "Field `ADDRESS_8_9` writer - 7-bit address or bits 7:1 of a 10-bit address"]
pub type Address8_9W<'a, REG> = crate::FieldWriter<'a, REG, 2>;
#[doc = "Field `ADDFORMAT` reader - Address mode for the I2C slave"]
pub type AddformatR = crate::BitReader;
#[doc = "Field `ADDFORMAT` writer - Address mode for the I2C slave"]
pub type AddformatW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ADDRESSEN` reader - I2C address enable"]
pub type AddressenR = crate::BitReader;
#[doc = "Field `ADDRESSEN` writer - I2C address enable"]
pub type AddressenW<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 0 - Bit 0 of a 10-bit address"]
    #[inline(always)]
    pub fn address_0(&self) -> Address0R {
        Address0R::new((self.bits & 1) != 0)
    }
    #[doc = "Bits 1:7 - Highest two bits of a 10-bit address"]
    #[inline(always)]
    pub fn address_1_7(&self) -> Address1_7R {
        Address1_7R::new(((self.bits >> 1) & 0x7f) as u8)
    }
    #[doc = "Bits 8:9 - 7-bit address or bits 7:1 of a 10-bit address"]
    #[inline(always)]
    pub fn address_8_9(&self) -> Address8_9R {
        Address8_9R::new(((self.bits >> 8) & 3) as u8)
    }
    #[doc = "Bit 10 - Address mode for the I2C slave"]
    #[inline(always)]
    pub fn addformat(&self) -> AddformatR {
        AddformatR::new(((self.bits >> 10) & 1) != 0)
    }
    #[doc = "Bit 15 - I2C address enable"]
    #[inline(always)]
    pub fn addressen(&self) -> AddressenR {
        AddressenR::new(((self.bits >> 15) & 1) != 0)
    }
}
impl W {
    #[doc = "Bit 0 - Bit 0 of a 10-bit address"]
    #[inline(always)]
    #[must_use]
    pub fn address_0(&mut self) -> Address0W<Saddr0Spec> {
        Address0W::new(self, 0)
    }
    #[doc = "Bits 1:7 - Highest two bits of a 10-bit address"]
    #[inline(always)]
    #[must_use]
    pub fn address_1_7(&mut self) -> Address1_7W<Saddr0Spec> {
        Address1_7W::new(self, 1)
    }
    #[doc = "Bits 8:9 - 7-bit address or bits 7:1 of a 10-bit address"]
    #[inline(always)]
    #[must_use]
    pub fn address_8_9(&mut self) -> Address8_9W<Saddr0Spec> {
        Address8_9W::new(self, 8)
    }
    #[doc = "Bit 10 - Address mode for the I2C slave"]
    #[inline(always)]
    #[must_use]
    pub fn addformat(&mut self) -> AddformatW<Saddr0Spec> {
        AddformatW::new(self, 10)
    }
    #[doc = "Bit 15 - I2C address enable"]
    #[inline(always)]
    #[must_use]
    pub fn addressen(&mut self) -> AddressenW<Saddr0Spec> {
        AddressenW::new(self, 15)
    }
}
#[doc = "Slave address register 0\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`saddr0::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`saddr0::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct Saddr0Spec;
impl crate::RegisterSpec for Saddr0Spec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`saddr0::R`](R) reader structure"]
impl crate::Readable for Saddr0Spec {}
#[doc = "`write(|w| ..)` method takes [`saddr0::W`](W) writer structure"]
impl crate::Writable for Saddr0Spec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets SADDR0 to value 0"]
impl crate::Resettable for Saddr0Spec {
    const RESET_VALUE: u32 = 0;
}
