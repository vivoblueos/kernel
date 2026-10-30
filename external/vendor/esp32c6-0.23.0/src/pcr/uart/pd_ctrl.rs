#[doc = "Register `PD_CTRL` reader"]
pub type R = crate::R<PD_CTRL_SPEC>;
#[doc = "Register `PD_CTRL` writer"]
pub type W = crate::W<PD_CTRL_SPEC>;
#[doc = "Field `MEM_FORCE_PU` reader - Set this bit to force power down UART0 memory."]
pub type MEM_FORCE_PU_R = crate::BitReader;
#[doc = "Field `MEM_FORCE_PU` writer - Set this bit to force power down UART0 memory."]
pub type MEM_FORCE_PU_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `MEM_FORCE_PD` reader - Set this bit to force power up UART0 memory."]
pub type MEM_FORCE_PD_R = crate::BitReader;
#[doc = "Field `MEM_FORCE_PD` writer - Set this bit to force power up UART0 memory."]
pub type MEM_FORCE_PD_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 1 - Set this bit to force power down UART0 memory."]
    #[inline(always)]
    pub fn mem_force_pu(&self) -> MEM_FORCE_PU_R {
        MEM_FORCE_PU_R::new(((self.bits >> 1) & 1) != 0)
    }
    #[doc = "Bit 2 - Set this bit to force power up UART0 memory."]
    #[inline(always)]
    pub fn mem_force_pd(&self) -> MEM_FORCE_PD_R {
        MEM_FORCE_PD_R::new(((self.bits >> 2) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("PD_CTRL")
            .field("mem_force_pu", &self.mem_force_pu())
            .field("mem_force_pd", &self.mem_force_pd())
            .finish()
    }
}
impl W {
    #[doc = "Bit 1 - Set this bit to force power down UART0 memory."]
    #[inline(always)]
    pub fn mem_force_pu(&mut self) -> MEM_FORCE_PU_W<'_, PD_CTRL_SPEC> {
        MEM_FORCE_PU_W::new(self, 1)
    }
    #[doc = "Bit 2 - Set this bit to force power up UART0 memory."]
    #[inline(always)]
    pub fn mem_force_pd(&mut self) -> MEM_FORCE_PD_W<'_, PD_CTRL_SPEC> {
        MEM_FORCE_PD_W::new(self, 2)
    }
}
#[doc = "UART0 power control register\n\nYou can [`read`](crate::Reg::read) this register and get [`pd_ctrl::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`pd_ctrl::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct PD_CTRL_SPEC;
impl crate::RegisterSpec for PD_CTRL_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`pd_ctrl::R`](R) reader structure"]
impl crate::Readable for PD_CTRL_SPEC {}
#[doc = "`write(|w| ..)` method takes [`pd_ctrl::W`](W) writer structure"]
impl crate::Writable for PD_CTRL_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets PD_CTRL to value 0x02"]
impl crate::Resettable for PD_CTRL_SPEC {
    const RESET_VALUE: u32 = 0x02;
}
