#[doc = "Register `INTF` reader"]
pub type R = crate::R<IntfSpec>;
#[doc = "Field `FLT0IF` reader - Fault 0 interrupt flag"]
pub type Flt0ifR = crate::BitReader;
#[doc = "Field `FLT1IF` reader - Fault 1 interrupt flag"]
pub type Flt1ifR = crate::BitReader;
#[doc = "Field `FLT2IF` reader - Fault 2 interrupt flag"]
pub type Flt2ifR = crate::BitReader;
#[doc = "Field `FLT3IF` reader - Fault 3 interrupt flag"]
pub type Flt3ifR = crate::BitReader;
#[doc = "Field `FLT4IF` reader - Fault 4 interrupt flag"]
pub type Flt4ifR = crate::BitReader;
#[doc = "Field `SYSFLTIF` reader - System fault interrupt flag"]
pub type SysfltifR = crate::BitReader;
#[doc = "Field `DLLCALIF` reader - DLL calibration completed interrupt flag"]
pub type DllcalifR = crate::BitReader;
#[doc = "Field `BMPERIF` reader - Bunch mode period interrupt flag"]
pub type BmperifR = crate::BitReader;
impl R {
    #[doc = "Bit 0 - Fault 0 interrupt flag"]
    #[inline(always)]
    pub fn flt0if(&self) -> Flt0ifR {
        Flt0ifR::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - Fault 1 interrupt flag"]
    #[inline(always)]
    pub fn flt1if(&self) -> Flt1ifR {
        Flt1ifR::new(((self.bits >> 1) & 1) != 0)
    }
    #[doc = "Bit 2 - Fault 2 interrupt flag"]
    #[inline(always)]
    pub fn flt2if(&self) -> Flt2ifR {
        Flt2ifR::new(((self.bits >> 2) & 1) != 0)
    }
    #[doc = "Bit 3 - Fault 3 interrupt flag"]
    #[inline(always)]
    pub fn flt3if(&self) -> Flt3ifR {
        Flt3ifR::new(((self.bits >> 3) & 1) != 0)
    }
    #[doc = "Bit 4 - Fault 4 interrupt flag"]
    #[inline(always)]
    pub fn flt4if(&self) -> Flt4ifR {
        Flt4ifR::new(((self.bits >> 4) & 1) != 0)
    }
    #[doc = "Bit 5 - System fault interrupt flag"]
    #[inline(always)]
    pub fn sysfltif(&self) -> SysfltifR {
        SysfltifR::new(((self.bits >> 5) & 1) != 0)
    }
    #[doc = "Bit 16 - DLL calibration completed interrupt flag"]
    #[inline(always)]
    pub fn dllcalif(&self) -> DllcalifR {
        DllcalifR::new(((self.bits >> 16) & 1) != 0)
    }
    #[doc = "Bit 17 - Bunch mode period interrupt flag"]
    #[inline(always)]
    pub fn bmperif(&self) -> BmperifR {
        BmperifR::new(((self.bits >> 17) & 1) != 0)
    }
}
#[doc = "SHRTIMER interrupt flag register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`intf::R`](R).  See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct IntfSpec;
impl crate::RegisterSpec for IntfSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`intf::R`](R) reader structure"]
impl crate::Readable for IntfSpec {}
#[doc = "`reset()` method sets INTF to value 0"]
impl crate::Resettable for IntfSpec {
    const RESET_VALUE: u32 = 0;
}
