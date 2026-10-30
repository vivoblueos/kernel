#[doc = "Register `CPU` reader"]
pub type R = crate::R<CPU_SPEC>;
#[doc = "Register `CPU` writer"]
pub type W = crate::W<CPU_SPEC>;
#[doc = "Field `LPCORE_DBGM_UNAVALIABLE` reader - need_des"]
pub type LPCORE_DBGM_UNAVALIABLE_R = crate::BitReader;
#[doc = "Field `LPCORE_DBGM_UNAVALIABLE` writer - need_des"]
pub type LPCORE_DBGM_UNAVALIABLE_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 31 - need_des"]
    #[inline(always)]
    pub fn lpcore_dbgm_unavaliable(&self) -> LPCORE_DBGM_UNAVALIABLE_R {
        LPCORE_DBGM_UNAVALIABLE_R::new(((self.bits >> 31) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("CPU")
            .field("lpcore_dbgm_unavaliable", &self.lpcore_dbgm_unavaliable())
            .finish()
    }
}
impl W {
    #[doc = "Bit 31 - need_des"]
    #[inline(always)]
    pub fn lpcore_dbgm_unavaliable(&mut self) -> LPCORE_DBGM_UNAVALIABLE_W<'_, CPU_SPEC> {
        LPCORE_DBGM_UNAVALIABLE_W::new(self, 31)
    }
}
#[doc = "need_des\n\nYou can [`read`](crate::Reg::read) this register and get [`cpu::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`cpu::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct CPU_SPEC;
impl crate::RegisterSpec for CPU_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`cpu::R`](R) reader structure"]
impl crate::Readable for CPU_SPEC {}
#[doc = "`write(|w| ..)` method takes [`cpu::W`](W) writer structure"]
impl crate::Writable for CPU_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets CPU to value 0x8000_0000"]
impl crate::Resettable for CPU_SPEC {
    const RESET_VALUE: u32 = 0x8000_0000;
}
