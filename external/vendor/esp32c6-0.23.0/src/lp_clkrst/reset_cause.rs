#[doc = "Register `RESET_CAUSE` reader"]
pub type R = crate::R<RESET_CAUSE_SPEC>;
#[doc = "Register `RESET_CAUSE` writer"]
pub type W = crate::W<RESET_CAUSE_SPEC>;
#[doc = "Field `RESET_CAUSE` reader - need_des"]
pub type RESET_CAUSE_R = crate::FieldReader;
#[doc = "Field `CORE0_RESET_FLAG` reader - need_des"]
pub type CORE0_RESET_FLAG_R = crate::BitReader;
#[doc = "Field `CORE0_RESET_CAUSE_CLR` writer - need_des"]
pub type CORE0_RESET_CAUSE_CLR_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `CORE0_RESET_FLAG_SET` writer - need_des"]
pub type CORE0_RESET_FLAG_SET_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `CORE0_RESET_FLAG_CLR` writer - need_des"]
pub type CORE0_RESET_FLAG_CLR_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bits 0:4 - need_des"]
    #[inline(always)]
    pub fn reset_cause(&self) -> RESET_CAUSE_R {
        RESET_CAUSE_R::new((self.bits & 0x1f) as u8)
    }
    #[doc = "Bit 5 - need_des"]
    #[inline(always)]
    pub fn core0_reset_flag(&self) -> CORE0_RESET_FLAG_R {
        CORE0_RESET_FLAG_R::new(((self.bits >> 5) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("RESET_CAUSE")
            .field("reset_cause", &self.reset_cause())
            .field("core0_reset_flag", &self.core0_reset_flag())
            .finish()
    }
}
impl W {
    #[doc = "Bit 29 - need_des"]
    #[inline(always)]
    pub fn core0_reset_cause_clr(&mut self) -> CORE0_RESET_CAUSE_CLR_W<'_, RESET_CAUSE_SPEC> {
        CORE0_RESET_CAUSE_CLR_W::new(self, 29)
    }
    #[doc = "Bit 30 - need_des"]
    #[inline(always)]
    pub fn core0_reset_flag_set(&mut self) -> CORE0_RESET_FLAG_SET_W<'_, RESET_CAUSE_SPEC> {
        CORE0_RESET_FLAG_SET_W::new(self, 30)
    }
    #[doc = "Bit 31 - need_des"]
    #[inline(always)]
    pub fn core0_reset_flag_clr(&mut self) -> CORE0_RESET_FLAG_CLR_W<'_, RESET_CAUSE_SPEC> {
        CORE0_RESET_FLAG_CLR_W::new(self, 31)
    }
}
#[doc = "need_des\n\nYou can [`read`](crate::Reg::read) this register and get [`reset_cause::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`reset_cause::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct RESET_CAUSE_SPEC;
impl crate::RegisterSpec for RESET_CAUSE_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`reset_cause::R`](R) reader structure"]
impl crate::Readable for RESET_CAUSE_SPEC {}
#[doc = "`write(|w| ..)` method takes [`reset_cause::W`](W) writer structure"]
impl crate::Writable for RESET_CAUSE_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets RESET_CAUSE to value 0x20"]
impl crate::Resettable for RESET_CAUSE_SPEC {
    const RESET_VALUE: u32 = 0x20;
}
