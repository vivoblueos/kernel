#[doc = "Register `SADDR0` reader"]
pub type R = crate::R<Saddr0Spec>;
#[doc = "Register `SADDR0` writer"]
pub type W = crate::W<Saddr0Spec>;
#[doc = "Field `ADDRESS0` reader - Bit 0 of a 10-bit address"]
pub type Address0R = crate::BitReader;
#[doc = "Field `ADDRESS0` writer - Bit 0 of a 10-bit address"]
pub type Address0W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ADDRESS7_1` reader - 7-bit address or bits 7:1 of a 10-bit address"]
pub type Address7_1R = crate::FieldReader;
#[doc = "Field `ADDRESS7_1` writer - 7-bit address or bits 7:1 of a 10-bit address"]
pub type Address7_1W<'a, REG> = crate::FieldWriter<'a, REG, 7>;
#[doc = "Field `ADDRESS9_8` reader - Highest two bits of a 10-bit address"]
pub type Address9_8R = crate::FieldReader;
#[doc = "Field `ADDRESS9_8` writer - Highest two bits of a 10-bit address"]
pub type Address9_8W<'a, REG> = crate::FieldWriter<'a, REG, 2>;
#[doc = "Field `ADDFORMAT` reader - Address mode for the I2C slave"]
pub type AddformatR = crate::BitReader;
#[doc = "Field `ADDFORMAT` writer - Address mode for the I2C slave"]
pub type AddformatW<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 0 - Bit 0 of a 10-bit address"]
    #[inline(always)]
    pub fn address0(&self) -> Address0R {
        Address0R::new((self.bits & 1) != 0)
    }
    #[doc = "Bits 1:7 - 7-bit address or bits 7:1 of a 10-bit address"]
    #[inline(always)]
    pub fn address7_1(&self) -> Address7_1R {
        Address7_1R::new(((self.bits >> 1) & 0x7f) as u8)
    }
    #[doc = "Bits 8:9 - Highest two bits of a 10-bit address"]
    #[inline(always)]
    pub fn address9_8(&self) -> Address9_8R {
        Address9_8R::new(((self.bits >> 8) & 3) as u8)
    }
    #[doc = "Bit 15 - Address mode for the I2C slave"]
    #[inline(always)]
    pub fn addformat(&self) -> AddformatR {
        AddformatR::new(((self.bits >> 15) & 1) != 0)
    }
}
impl W {
    #[doc = "Bit 0 - Bit 0 of a 10-bit address"]
    #[inline(always)]
    #[must_use]
    pub fn address0(&mut self) -> Address0W<Saddr0Spec> {
        Address0W::new(self, 0)
    }
    #[doc = "Bits 1:7 - 7-bit address or bits 7:1 of a 10-bit address"]
    #[inline(always)]
    #[must_use]
    pub fn address7_1(&mut self) -> Address7_1W<Saddr0Spec> {
        Address7_1W::new(self, 1)
    }
    #[doc = "Bits 8:9 - Highest two bits of a 10-bit address"]
    #[inline(always)]
    #[must_use]
    pub fn address9_8(&mut self) -> Address9_8W<Saddr0Spec> {
        Address9_8W::new(self, 8)
    }
    #[doc = "Bit 15 - Address mode for the I2C slave"]
    #[inline(always)]
    #[must_use]
    pub fn addformat(&mut self) -> AddformatW<Saddr0Spec> {
        AddformatW::new(self, 15)
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
