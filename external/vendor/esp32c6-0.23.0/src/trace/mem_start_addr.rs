#[doc = "Register `MEM_START_ADDR` reader"]
pub type R = crate::R<MEM_START_ADDR_SPEC>;
#[doc = "Register `MEM_START_ADDR` writer"]
pub type W = crate::W<MEM_START_ADDR_SPEC>;
#[doc = "Field `MEM_START_ADDR` reader - The start address of trace memory"]
pub type MEM_START_ADDR_R = crate::FieldReader<u32>;
#[doc = "Field `MEM_START_ADDR` writer - The start address of trace memory"]
pub type MEM_START_ADDR_W<'a, REG> = crate::FieldWriter<'a, REG, 32, u32>;
impl R {
    #[doc = "Bits 0:31 - The start address of trace memory"]
    #[inline(always)]
    pub fn mem_start_addr(&self) -> MEM_START_ADDR_R {
        MEM_START_ADDR_R::new(self.bits)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("MEM_START_ADDR")
            .field("mem_start_addr", &self.mem_start_addr())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:31 - The start address of trace memory"]
    #[inline(always)]
    pub fn mem_start_addr(&mut self) -> MEM_START_ADDR_W<'_, MEM_START_ADDR_SPEC> {
        MEM_START_ADDR_W::new(self, 0)
    }
}
#[doc = "mem start addr\n\nYou can [`read`](crate::Reg::read) this register and get [`mem_start_addr::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`mem_start_addr::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct MEM_START_ADDR_SPEC;
impl crate::RegisterSpec for MEM_START_ADDR_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`mem_start_addr::R`](R) reader structure"]
impl crate::Readable for MEM_START_ADDR_SPEC {}
#[doc = "`write(|w| ..)` method takes [`mem_start_addr::W`](W) writer structure"]
impl crate::Writable for MEM_START_ADDR_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets MEM_START_ADDR to value 0"]
impl crate::Resettable for MEM_START_ADDR_SPEC {}
