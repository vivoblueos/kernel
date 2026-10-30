#[doc = "Register `FH_STATUS` reader"]
pub type R = crate::R<FH_STATUS_SPEC>;
#[doc = "Field `CBC_ON` reader - Set and reset by hardware. If set, a cycle-by-cycle mode action is on going"]
pub type CBC_ON_R = crate::BitReader;
#[doc = "Field `OST_ON` reader - Set and reset by hardware. If set, an one-shot mode action is on going"]
pub type OST_ON_R = crate::BitReader;
impl R {
    #[doc = "Bit 0 - Set and reset by hardware. If set, a cycle-by-cycle mode action is on going"]
    #[inline(always)]
    pub fn cbc_on(&self) -> CBC_ON_R {
        CBC_ON_R::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - Set and reset by hardware. If set, an one-shot mode action is on going"]
    #[inline(always)]
    pub fn ost_on(&self) -> OST_ON_R {
        OST_ON_R::new(((self.bits >> 1) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("FH_STATUS")
            .field("cbc_on", &self.cbc_on())
            .field("ost_on", &self.ost_on())
            .finish()
    }
}
#[doc = "Status of fault events.\n\nYou can [`read`](crate::Reg::read) this register and get [`fh_status::R`](R). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct FH_STATUS_SPEC;
impl crate::RegisterSpec for FH_STATUS_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`fh_status::R`](R) reader structure"]
impl crate::Readable for FH_STATUS_SPEC {}
#[doc = "`reset()` method sets FH_STATUS to value 0"]
impl crate::Resettable for FH_STATUS_SPEC {}
