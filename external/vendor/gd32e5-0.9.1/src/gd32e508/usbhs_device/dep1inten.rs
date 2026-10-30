#[doc = "Register `DEP1INTEN` reader"]
pub type R = crate::R<Dep1intenSpec>;
#[doc = "Field `IEP1INTEN` reader - IN Endpoint 1 interrupt enable"]
pub type Iep1intenR = crate::BitReader;
#[doc = "Field `OEP1INTEN` reader - OUT Endpoint 1 interrupt enable"]
pub type Oep1intenR = crate::BitReader;
impl R {
    #[doc = "Bit 1 - IN Endpoint 1 interrupt enable"]
    #[inline(always)]
    pub fn iep1inten(&self) -> Iep1intenR {
        Iep1intenR::new(((self.bits >> 1) & 1) != 0)
    }
    #[doc = "Bit 17 - OUT Endpoint 1 interrupt enable"]
    #[inline(always)]
    pub fn oep1inten(&self) -> Oep1intenR {
        Oep1intenR::new(((self.bits >> 17) & 1) != 0)
    }
}
#[doc = "Device endpoint 1 interrupt register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`dep1inten::R`](R).  See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct Dep1intenSpec;
impl crate::RegisterSpec for Dep1intenSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`dep1inten::R`](R) reader structure"]
impl crate::Readable for Dep1intenSpec {}
#[doc = "`reset()` method sets DEP1INTEN to value 0"]
impl crate::Resettable for Dep1intenSpec {
    const RESET_VALUE: u32 = 0;
}
