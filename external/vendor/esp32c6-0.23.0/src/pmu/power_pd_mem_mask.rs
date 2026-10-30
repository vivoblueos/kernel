#[doc = "Register `POWER_PD_MEM_MASK` reader"]
pub type R = crate::R<POWER_PD_MEM_MASK_SPEC>;
#[doc = "Register `POWER_PD_MEM_MASK` writer"]
pub type W = crate::W<POWER_PD_MEM_MASK_SPEC>;
#[doc = "Field `PD_HP_MEM2_PD_MASK` reader - need_des"]
pub type PD_HP_MEM2_PD_MASK_R = crate::FieldReader;
#[doc = "Field `PD_HP_MEM2_PD_MASK` writer - need_des"]
pub type PD_HP_MEM2_PD_MASK_W<'a, REG> = crate::FieldWriter<'a, REG, 5>;
#[doc = "Field `PD_HP_MEM1_PD_MASK` reader - need_des"]
pub type PD_HP_MEM1_PD_MASK_R = crate::FieldReader;
#[doc = "Field `PD_HP_MEM1_PD_MASK` writer - need_des"]
pub type PD_HP_MEM1_PD_MASK_W<'a, REG> = crate::FieldWriter<'a, REG, 5>;
#[doc = "Field `PD_HP_MEM0_PD_MASK` reader - need_des"]
pub type PD_HP_MEM0_PD_MASK_R = crate::FieldReader;
#[doc = "Field `PD_HP_MEM0_PD_MASK` writer - need_des"]
pub type PD_HP_MEM0_PD_MASK_W<'a, REG> = crate::FieldWriter<'a, REG, 5>;
#[doc = "Field `PD_HP_MEM2_MASK` reader - need_des"]
pub type PD_HP_MEM2_MASK_R = crate::FieldReader;
#[doc = "Field `PD_HP_MEM2_MASK` writer - need_des"]
pub type PD_HP_MEM2_MASK_W<'a, REG> = crate::FieldWriter<'a, REG, 5>;
#[doc = "Field `PD_HP_MEM1_MASK` reader - need_des"]
pub type PD_HP_MEM1_MASK_R = crate::FieldReader;
#[doc = "Field `PD_HP_MEM1_MASK` writer - need_des"]
pub type PD_HP_MEM1_MASK_W<'a, REG> = crate::FieldWriter<'a, REG, 5>;
#[doc = "Field `PD_HP_MEM0_MASK` reader - need_des"]
pub type PD_HP_MEM0_MASK_R = crate::FieldReader;
#[doc = "Field `PD_HP_MEM0_MASK` writer - need_des"]
pub type PD_HP_MEM0_MASK_W<'a, REG> = crate::FieldWriter<'a, REG, 5>;
impl R {
    #[doc = "Bits 0:4 - need_des"]
    #[inline(always)]
    pub fn pd_hp_mem2_pd_mask(&self) -> PD_HP_MEM2_PD_MASK_R {
        PD_HP_MEM2_PD_MASK_R::new((self.bits & 0x1f) as u8)
    }
    #[doc = "Bits 5:9 - need_des"]
    #[inline(always)]
    pub fn pd_hp_mem1_pd_mask(&self) -> PD_HP_MEM1_PD_MASK_R {
        PD_HP_MEM1_PD_MASK_R::new(((self.bits >> 5) & 0x1f) as u8)
    }
    #[doc = "Bits 10:14 - need_des"]
    #[inline(always)]
    pub fn pd_hp_mem0_pd_mask(&self) -> PD_HP_MEM0_PD_MASK_R {
        PD_HP_MEM0_PD_MASK_R::new(((self.bits >> 10) & 0x1f) as u8)
    }
    #[doc = "Bits 17:21 - need_des"]
    #[inline(always)]
    pub fn pd_hp_mem2_mask(&self) -> PD_HP_MEM2_MASK_R {
        PD_HP_MEM2_MASK_R::new(((self.bits >> 17) & 0x1f) as u8)
    }
    #[doc = "Bits 22:26 - need_des"]
    #[inline(always)]
    pub fn pd_hp_mem1_mask(&self) -> PD_HP_MEM1_MASK_R {
        PD_HP_MEM1_MASK_R::new(((self.bits >> 22) & 0x1f) as u8)
    }
    #[doc = "Bits 27:31 - need_des"]
    #[inline(always)]
    pub fn pd_hp_mem0_mask(&self) -> PD_HP_MEM0_MASK_R {
        PD_HP_MEM0_MASK_R::new(((self.bits >> 27) & 0x1f) as u8)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("POWER_PD_MEM_MASK")
            .field("pd_hp_mem2_pd_mask", &self.pd_hp_mem2_pd_mask())
            .field("pd_hp_mem1_pd_mask", &self.pd_hp_mem1_pd_mask())
            .field("pd_hp_mem0_pd_mask", &self.pd_hp_mem0_pd_mask())
            .field("pd_hp_mem2_mask", &self.pd_hp_mem2_mask())
            .field("pd_hp_mem1_mask", &self.pd_hp_mem1_mask())
            .field("pd_hp_mem0_mask", &self.pd_hp_mem0_mask())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:4 - need_des"]
    #[inline(always)]
    pub fn pd_hp_mem2_pd_mask(&mut self) -> PD_HP_MEM2_PD_MASK_W<'_, POWER_PD_MEM_MASK_SPEC> {
        PD_HP_MEM2_PD_MASK_W::new(self, 0)
    }
    #[doc = "Bits 5:9 - need_des"]
    #[inline(always)]
    pub fn pd_hp_mem1_pd_mask(&mut self) -> PD_HP_MEM1_PD_MASK_W<'_, POWER_PD_MEM_MASK_SPEC> {
        PD_HP_MEM1_PD_MASK_W::new(self, 5)
    }
    #[doc = "Bits 10:14 - need_des"]
    #[inline(always)]
    pub fn pd_hp_mem0_pd_mask(&mut self) -> PD_HP_MEM0_PD_MASK_W<'_, POWER_PD_MEM_MASK_SPEC> {
        PD_HP_MEM0_PD_MASK_W::new(self, 10)
    }
    #[doc = "Bits 17:21 - need_des"]
    #[inline(always)]
    pub fn pd_hp_mem2_mask(&mut self) -> PD_HP_MEM2_MASK_W<'_, POWER_PD_MEM_MASK_SPEC> {
        PD_HP_MEM2_MASK_W::new(self, 17)
    }
    #[doc = "Bits 22:26 - need_des"]
    #[inline(always)]
    pub fn pd_hp_mem1_mask(&mut self) -> PD_HP_MEM1_MASK_W<'_, POWER_PD_MEM_MASK_SPEC> {
        PD_HP_MEM1_MASK_W::new(self, 22)
    }
    #[doc = "Bits 27:31 - need_des"]
    #[inline(always)]
    pub fn pd_hp_mem0_mask(&mut self) -> PD_HP_MEM0_MASK_W<'_, POWER_PD_MEM_MASK_SPEC> {
        PD_HP_MEM0_MASK_W::new(self, 27)
    }
}
#[doc = "need_des\n\nYou can [`read`](crate::Reg::read) this register and get [`power_pd_mem_mask::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`power_pd_mem_mask::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct POWER_PD_MEM_MASK_SPEC;
impl crate::RegisterSpec for POWER_PD_MEM_MASK_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`power_pd_mem_mask::R`](R) reader structure"]
impl crate::Readable for POWER_PD_MEM_MASK_SPEC {}
#[doc = "`write(|w| ..)` method takes [`power_pd_mem_mask::W`](W) writer structure"]
impl crate::Writable for POWER_PD_MEM_MASK_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets POWER_PD_MEM_MASK to value 0"]
impl crate::Resettable for POWER_PD_MEM_MASK_SPEC {}
