#[doc = "Register `MEM_END_ADDR` reader"]
pub type R = crate::R<MEM_END_ADDR_SPEC>;
#[doc = "Register `MEM_END_ADDR` writer"]
pub type W = crate::W<MEM_END_ADDR_SPEC>;
#[doc = "Field `MEM_END_ADDR` reader - The end address of trace memory"]
pub type MEM_END_ADDR_R = crate::FieldReader<u32>;
#[doc = "Field `MEM_END_ADDR` writer - The end address of trace memory"]
pub type MEM_END_ADDR_W<'a, REG> = crate::FieldWriter<'a, REG, 32, u32>;
impl R {
    #[doc = "Bits 0:31 - The end address of trace memory"]
    #[inline(always)]
    pub fn mem_end_addr(&self) -> MEM_END_ADDR_R {
        MEM_END_ADDR_R::new(self.bits)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("MEM_END_ADDR")
            .field("mem_end_addr", &self.mem_end_addr())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:31 - The end address of trace memory"]
    #[inline(always)]
    pub fn mem_end_addr(&mut self) -> MEM_END_ADDR_W<'_, MEM_END_ADDR_SPEC> {
        MEM_END_ADDR_W::new(self, 0)
    }
}
#[doc = "mem end addr\n\nYou can [`read`](crate::Reg::read) this register and get [`mem_end_addr::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`mem_end_addr::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct MEM_END_ADDR_SPEC;
impl crate::RegisterSpec for MEM_END_ADDR_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`mem_end_addr::R`](R) reader structure"]
impl crate::Readable for MEM_END_ADDR_SPEC {}
#[doc = "`write(|w| ..)` method takes [`mem_end_addr::W`](W) writer structure"]
impl crate::Writable for MEM_END_ADDR_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets MEM_END_ADDR to value 0xffff_ffff"]
impl crate::Resettable for MEM_END_ADDR_SPEC {
    const RESET_VALUE: u32 = 0xffff_ffff;
}
