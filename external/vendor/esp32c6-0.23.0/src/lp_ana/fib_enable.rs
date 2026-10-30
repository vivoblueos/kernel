#[doc = "Register `FIB_ENABLE` reader"]
pub type R = crate::R<FIB_ENABLE_SPEC>;
#[doc = "Register `FIB_ENABLE` writer"]
pub type W = crate::W<FIB_ENABLE_SPEC>;
#[doc = "Field `ANA_FIB_ENA` reader - need_des"]
pub type ANA_FIB_ENA_R = crate::FieldReader<u32>;
#[doc = "Field `ANA_FIB_ENA` writer - need_des"]
pub type ANA_FIB_ENA_W<'a, REG> = crate::FieldWriter<'a, REG, 32, u32>;
impl R {
    #[doc = "Bits 0:31 - need_des"]
    #[inline(always)]
    pub fn ana_fib_ena(&self) -> ANA_FIB_ENA_R {
        ANA_FIB_ENA_R::new(self.bits)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("FIB_ENABLE")
            .field("ana_fib_ena", &self.ana_fib_ena())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:31 - need_des"]
    #[inline(always)]
    pub fn ana_fib_ena(&mut self) -> ANA_FIB_ENA_W<'_, FIB_ENABLE_SPEC> {
        ANA_FIB_ENA_W::new(self, 0)
    }
}
#[doc = "need_des\n\nYou can [`read`](crate::Reg::read) this register and get [`fib_enable::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`fib_enable::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct FIB_ENABLE_SPEC;
impl crate::RegisterSpec for FIB_ENABLE_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`fib_enable::R`](R) reader structure"]
impl crate::Readable for FIB_ENABLE_SPEC {}
#[doc = "`write(|w| ..)` method takes [`fib_enable::W`](W) writer structure"]
impl crate::Writable for FIB_ENABLE_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets FIB_ENABLE to value 0xffff_ffff"]
impl crate::Resettable for FIB_ENABLE_SPEC {
    const RESET_VALUE: u32 = 0xffff_ffff;
}
