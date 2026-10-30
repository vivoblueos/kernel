#[doc = "Register `FPGA_DEBUG` reader"]
pub type R = crate::R<FPGA_DEBUG_SPEC>;
#[doc = "Register `FPGA_DEBUG` writer"]
pub type W = crate::W<FPGA_DEBUG_SPEC>;
#[doc = "Field `FPGA_DEBUG` reader - Only used in fpga debug."]
pub type FPGA_DEBUG_R = crate::FieldReader<u32>;
#[doc = "Field `FPGA_DEBUG` writer - Only used in fpga debug."]
pub type FPGA_DEBUG_W<'a, REG> = crate::FieldWriter<'a, REG, 32, u32>;
impl R {
    #[doc = "Bits 0:31 - Only used in fpga debug."]
    #[inline(always)]
    pub fn fpga_debug(&self) -> FPGA_DEBUG_R {
        FPGA_DEBUG_R::new(self.bits)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("FPGA_DEBUG")
            .field("fpga_debug", &self.fpga_debug())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:31 - Only used in fpga debug."]
    #[inline(always)]
    pub fn fpga_debug(&mut self) -> FPGA_DEBUG_W<'_, FPGA_DEBUG_SPEC> {
        FPGA_DEBUG_W::new(self, 0)
    }
}
#[doc = "fpga debug register\n\nYou can [`read`](crate::Reg::read) this register and get [`fpga_debug::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`fpga_debug::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct FPGA_DEBUG_SPEC;
impl crate::RegisterSpec for FPGA_DEBUG_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`fpga_debug::R`](R) reader structure"]
impl crate::Readable for FPGA_DEBUG_SPEC {}
#[doc = "`write(|w| ..)` method takes [`fpga_debug::W`](W) writer structure"]
impl crate::Writable for FPGA_DEBUG_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets FPGA_DEBUG to value 0xffff_ffff"]
impl crate::Resettable for FPGA_DEBUG_SPEC {
    const RESET_VALUE: u32 = 0xffff_ffff;
}
