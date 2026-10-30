#[doc = "Register `DBG_SEL` reader"]
pub type R = crate::R<DBG_SEL_SPEC>;
#[doc = "Register `DBG_SEL` writer"]
pub type W = crate::W<DBG_SEL_SPEC>;
#[doc = "Field `DEBUG_12M_NO_GATING` reader - use for debug"]
pub type DEBUG_12M_NO_GATING_R = crate::BitReader;
#[doc = "Field `DEBUG_12M_NO_GATING` writer - use for debug"]
pub type DEBUG_12M_NO_GATING_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `DEBUG_BIT_SEL` reader - use for debug"]
pub type DEBUG_BIT_SEL_R = crate::FieldReader;
#[doc = "Field `DEBUG_BIT_SEL` writer - use for debug"]
pub type DEBUG_BIT_SEL_W<'a, REG> = crate::FieldWriter<'a, REG, 5>;
#[doc = "Field `DEBUG_SEL0` reader - use for debug"]
pub type DEBUG_SEL0_R = crate::FieldReader;
#[doc = "Field `DEBUG_SEL0` writer - use for debug"]
pub type DEBUG_SEL0_W<'a, REG> = crate::FieldWriter<'a, REG, 5>;
#[doc = "Field `DEBUG_SEL1` reader - use for debug"]
pub type DEBUG_SEL1_R = crate::FieldReader;
#[doc = "Field `DEBUG_SEL1` writer - use for debug"]
pub type DEBUG_SEL1_W<'a, REG> = crate::FieldWriter<'a, REG, 5>;
#[doc = "Field `DEBUG_SEL2` reader - use for debug"]
pub type DEBUG_SEL2_R = crate::FieldReader;
#[doc = "Field `DEBUG_SEL2` writer - use for debug"]
pub type DEBUG_SEL2_W<'a, REG> = crate::FieldWriter<'a, REG, 5>;
#[doc = "Field `DEBUG_SEL3` reader - use for debug"]
pub type DEBUG_SEL3_R = crate::FieldReader;
#[doc = "Field `DEBUG_SEL3` writer - use for debug"]
pub type DEBUG_SEL3_W<'a, REG> = crate::FieldWriter<'a, REG, 5>;
#[doc = "Field `DEBUG_SEL4` reader - use for debug"]
pub type DEBUG_SEL4_R = crate::FieldReader;
#[doc = "Field `DEBUG_SEL4` writer - use for debug"]
pub type DEBUG_SEL4_W<'a, REG> = crate::FieldWriter<'a, REG, 5>;
impl R {
    #[doc = "Bit 1 - use for debug"]
    #[inline(always)]
    pub fn debug_12m_no_gating(&self) -> DEBUG_12M_NO_GATING_R {
        DEBUG_12M_NO_GATING_R::new(((self.bits >> 1) & 1) != 0)
    }
    #[doc = "Bits 2:6 - use for debug"]
    #[inline(always)]
    pub fn debug_bit_sel(&self) -> DEBUG_BIT_SEL_R {
        DEBUG_BIT_SEL_R::new(((self.bits >> 2) & 0x1f) as u8)
    }
    #[doc = "Bits 7:11 - use for debug"]
    #[inline(always)]
    pub fn debug_sel0(&self) -> DEBUG_SEL0_R {
        DEBUG_SEL0_R::new(((self.bits >> 7) & 0x1f) as u8)
    }
    #[doc = "Bits 12:16 - use for debug"]
    #[inline(always)]
    pub fn debug_sel1(&self) -> DEBUG_SEL1_R {
        DEBUG_SEL1_R::new(((self.bits >> 12) & 0x1f) as u8)
    }
    #[doc = "Bits 17:21 - use for debug"]
    #[inline(always)]
    pub fn debug_sel2(&self) -> DEBUG_SEL2_R {
        DEBUG_SEL2_R::new(((self.bits >> 17) & 0x1f) as u8)
    }
    #[doc = "Bits 22:26 - use for debug"]
    #[inline(always)]
    pub fn debug_sel3(&self) -> DEBUG_SEL3_R {
        DEBUG_SEL3_R::new(((self.bits >> 22) & 0x1f) as u8)
    }
    #[doc = "Bits 27:31 - use for debug"]
    #[inline(always)]
    pub fn debug_sel4(&self) -> DEBUG_SEL4_R {
        DEBUG_SEL4_R::new(((self.bits >> 27) & 0x1f) as u8)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("DBG_SEL")
            .field("debug_12m_no_gating", &self.debug_12m_no_gating())
            .field("debug_bit_sel", &self.debug_bit_sel())
            .field("debug_sel0", &self.debug_sel0())
            .field("debug_sel1", &self.debug_sel1())
            .field("debug_sel2", &self.debug_sel2())
            .field("debug_sel3", &self.debug_sel3())
            .field("debug_sel4", &self.debug_sel4())
            .finish()
    }
}
impl W {
    #[doc = "Bit 1 - use for debug"]
    #[inline(always)]
    pub fn debug_12m_no_gating(&mut self) -> DEBUG_12M_NO_GATING_W<'_, DBG_SEL_SPEC> {
        DEBUG_12M_NO_GATING_W::new(self, 1)
    }
    #[doc = "Bits 2:6 - use for debug"]
    #[inline(always)]
    pub fn debug_bit_sel(&mut self) -> DEBUG_BIT_SEL_W<'_, DBG_SEL_SPEC> {
        DEBUG_BIT_SEL_W::new(self, 2)
    }
    #[doc = "Bits 7:11 - use for debug"]
    #[inline(always)]
    pub fn debug_sel0(&mut self) -> DEBUG_SEL0_W<'_, DBG_SEL_SPEC> {
        DEBUG_SEL0_W::new(self, 7)
    }
    #[doc = "Bits 12:16 - use for debug"]
    #[inline(always)]
    pub fn debug_sel1(&mut self) -> DEBUG_SEL1_W<'_, DBG_SEL_SPEC> {
        DEBUG_SEL1_W::new(self, 12)
    }
    #[doc = "Bits 17:21 - use for debug"]
    #[inline(always)]
    pub fn debug_sel2(&mut self) -> DEBUG_SEL2_W<'_, DBG_SEL_SPEC> {
        DEBUG_SEL2_W::new(self, 17)
    }
    #[doc = "Bits 22:26 - use for debug"]
    #[inline(always)]
    pub fn debug_sel3(&mut self) -> DEBUG_SEL3_W<'_, DBG_SEL_SPEC> {
        DEBUG_SEL3_W::new(self, 22)
    }
    #[doc = "Bits 27:31 - use for debug"]
    #[inline(always)]
    pub fn debug_sel4(&mut self) -> DEBUG_SEL4_W<'_, DBG_SEL_SPEC> {
        DEBUG_SEL4_W::new(self, 27)
    }
}
#[doc = "rtc configure register\n\nYou can [`read`](crate::Reg::read) this register and get [`dbg_sel::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`dbg_sel::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct DBG_SEL_SPEC;
impl crate::RegisterSpec for DBG_SEL_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`dbg_sel::R`](R) reader structure"]
impl crate::Readable for DBG_SEL_SPEC {}
#[doc = "`write(|w| ..)` method takes [`dbg_sel::W`](W) writer structure"]
impl crate::Writable for DBG_SEL_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets DBG_SEL to value 0"]
impl crate::Resettable for DBG_SEL_SPEC {}
