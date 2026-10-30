#[doc = "Register `DEP1INT` reader"]
pub type R = crate::R<Dep1intSpec>;
#[doc = "Field `IEP1INT` reader - IN Endpoint 1 interrupt"]
pub type Iep1intR = crate::BitReader;
#[doc = "Field `OEP1INT` reader - OUT Endpoint 1 interrupt"]
pub type Oep1intR = crate::BitReader;
impl R {
    #[doc = "Bit 1 - IN Endpoint 1 interrupt"]
    #[inline(always)]
    pub fn iep1int(&self) -> Iep1intR {
        Iep1intR::new(((self.bits >> 1) & 1) != 0)
    }
    #[doc = "Bit 17 - OUT Endpoint 1 interrupt"]
    #[inline(always)]
    pub fn oep1int(&self) -> Oep1intR {
        Oep1intR::new(((self.bits >> 17) & 1) != 0)
    }
}
#[doc = "Device endpoint 1 interrupt register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`dep1int::R`](R).  See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct Dep1intSpec;
impl crate::RegisterSpec for Dep1intSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`dep1int::R`](R) reader structure"]
impl crate::Readable for Dep1intSpec {}
#[doc = "`reset()` method sets DEP1INT to value 0"]
impl crate::Resettable for Dep1intSpec {
    const RESET_VALUE: u32 = 0;
}
