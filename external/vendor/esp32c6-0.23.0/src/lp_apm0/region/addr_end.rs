#[doc = "Register `ADDR_END` reader"]
pub type R = crate::R<ADDR_END_SPEC>;
#[doc = "Register `ADDR_END` writer"]
pub type W = crate::W<ADDR_END_SPEC>;
#[doc = "Field `ADDR_END` reader - End address of region0"]
pub type ADDR_END_R = crate::FieldReader<u32>;
#[doc = "Field `ADDR_END` writer - End address of region0"]
pub type ADDR_END_W<'a, REG> = crate::FieldWriter<'a, REG, 32, u32>;
impl R {
    #[doc = "Bits 0:31 - End address of region0"]
    #[inline(always)]
    pub fn addr_end(&self) -> ADDR_END_R {
        ADDR_END_R::new(self.bits)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("ADDR_END")
            .field("addr_end", &self.addr_end())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:31 - End address of region0"]
    #[inline(always)]
    pub fn addr_end(&mut self) -> ADDR_END_W<'_, ADDR_END_SPEC> {
        ADDR_END_W::new(self, 0)
    }
}
#[doc = "Region address register\n\nYou can [`read`](crate::Reg::read) this register and get [`addr_end::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`addr_end::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct ADDR_END_SPEC;
impl crate::RegisterSpec for ADDR_END_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`addr_end::R`](R) reader structure"]
impl crate::Readable for ADDR_END_SPEC {}
#[doc = "`write(|w| ..)` method takes [`addr_end::W`](W) writer structure"]
impl crate::Writable for ADDR_END_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets ADDR_END to value 0xffff_ffff"]
impl crate::Resettable for ADDR_END_SPEC {
    const RESET_VALUE: u32 = 0xffff_ffff;
}
