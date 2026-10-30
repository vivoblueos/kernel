#[doc = "Register `ECC_PD_CTRL` reader"]
pub type R = crate::R<ECC_PD_CTRL_SPEC>;
#[doc = "Register `ECC_PD_CTRL` writer"]
pub type W = crate::W<ECC_PD_CTRL_SPEC>;
#[doc = "Field `ECC_MEM_PD` reader - Set this bit to power down ecc internal memory."]
pub type ECC_MEM_PD_R = crate::BitReader;
#[doc = "Field `ECC_MEM_PD` writer - Set this bit to power down ecc internal memory."]
pub type ECC_MEM_PD_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ECC_MEM_FORCE_PU` reader - Set this bit to force power up ecc internal memory"]
pub type ECC_MEM_FORCE_PU_R = crate::BitReader;
#[doc = "Field `ECC_MEM_FORCE_PU` writer - Set this bit to force power up ecc internal memory"]
pub type ECC_MEM_FORCE_PU_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ECC_MEM_FORCE_PD` reader - Set this bit to force power down ecc internal memory."]
pub type ECC_MEM_FORCE_PD_R = crate::BitReader;
#[doc = "Field `ECC_MEM_FORCE_PD` writer - Set this bit to force power down ecc internal memory."]
pub type ECC_MEM_FORCE_PD_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 0 - Set this bit to power down ecc internal memory."]
    #[inline(always)]
    pub fn ecc_mem_pd(&self) -> ECC_MEM_PD_R {
        ECC_MEM_PD_R::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - Set this bit to force power up ecc internal memory"]
    #[inline(always)]
    pub fn ecc_mem_force_pu(&self) -> ECC_MEM_FORCE_PU_R {
        ECC_MEM_FORCE_PU_R::new(((self.bits >> 1) & 1) != 0)
    }
    #[doc = "Bit 2 - Set this bit to force power down ecc internal memory."]
    #[inline(always)]
    pub fn ecc_mem_force_pd(&self) -> ECC_MEM_FORCE_PD_R {
        ECC_MEM_FORCE_PD_R::new(((self.bits >> 2) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("ECC_PD_CTRL")
            .field("ecc_mem_pd", &self.ecc_mem_pd())
            .field("ecc_mem_force_pu", &self.ecc_mem_force_pu())
            .field("ecc_mem_force_pd", &self.ecc_mem_force_pd())
            .finish()
    }
}
impl W {
    #[doc = "Bit 0 - Set this bit to power down ecc internal memory."]
    #[inline(always)]
    pub fn ecc_mem_pd(&mut self) -> ECC_MEM_PD_W<'_, ECC_PD_CTRL_SPEC> {
        ECC_MEM_PD_W::new(self, 0)
    }
    #[doc = "Bit 1 - Set this bit to force power up ecc internal memory"]
    #[inline(always)]
    pub fn ecc_mem_force_pu(&mut self) -> ECC_MEM_FORCE_PU_W<'_, ECC_PD_CTRL_SPEC> {
        ECC_MEM_FORCE_PU_W::new(self, 1)
    }
    #[doc = "Bit 2 - Set this bit to force power down ecc internal memory."]
    #[inline(always)]
    pub fn ecc_mem_force_pd(&mut self) -> ECC_MEM_FORCE_PD_W<'_, ECC_PD_CTRL_SPEC> {
        ECC_MEM_FORCE_PD_W::new(self, 2)
    }
}
#[doc = "ECC power control register\n\nYou can [`read`](crate::Reg::read) this register and get [`ecc_pd_ctrl::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`ecc_pd_ctrl::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct ECC_PD_CTRL_SPEC;
impl crate::RegisterSpec for ECC_PD_CTRL_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`ecc_pd_ctrl::R`](R) reader structure"]
impl crate::Readable for ECC_PD_CTRL_SPEC {}
#[doc = "`write(|w| ..)` method takes [`ecc_pd_ctrl::W`](W) writer structure"]
impl crate::Writable for ECC_PD_CTRL_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets ECC_PD_CTRL to value 0x02"]
impl crate::Resettable for ECC_PD_CTRL_SPEC {
    const RESET_VALUE: u32 = 0x02;
}
