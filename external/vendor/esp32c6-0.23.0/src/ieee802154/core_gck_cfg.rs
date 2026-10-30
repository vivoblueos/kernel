#[doc = "Register `CORE_GCK_CFG` reader"]
pub type R = crate::R<CORE_GCK_CFG_SPEC>;
#[doc = "Register `CORE_GCK_CFG` writer"]
pub type W = crate::W<CORE_GCK_CFG_SPEC>;
#[doc = "Field `DIS_PKT_GCK` reader - "]
pub type DIS_PKT_GCK_R = crate::BitReader;
#[doc = "Field `DIS_PKT_GCK` writer - "]
pub type DIS_PKT_GCK_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `DIS_CTRL_GCK` reader - "]
pub type DIS_CTRL_GCK_R = crate::BitReader;
#[doc = "Field `DIS_CTRL_GCK` writer - "]
pub type DIS_CTRL_GCK_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 0"]
    #[inline(always)]
    pub fn dis_pkt_gck(&self) -> DIS_PKT_GCK_R {
        DIS_PKT_GCK_R::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1"]
    #[inline(always)]
    pub fn dis_ctrl_gck(&self) -> DIS_CTRL_GCK_R {
        DIS_CTRL_GCK_R::new(((self.bits >> 1) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("CORE_GCK_CFG")
            .field("dis_pkt_gck", &self.dis_pkt_gck())
            .field("dis_ctrl_gck", &self.dis_ctrl_gck())
            .finish()
    }
}
impl W {
    #[doc = "Bit 0"]
    #[inline(always)]
    pub fn dis_pkt_gck(&mut self) -> DIS_PKT_GCK_W<'_, CORE_GCK_CFG_SPEC> {
        DIS_PKT_GCK_W::new(self, 0)
    }
    #[doc = "Bit 1"]
    #[inline(always)]
    pub fn dis_ctrl_gck(&mut self) -> DIS_CTRL_GCK_W<'_, CORE_GCK_CFG_SPEC> {
        DIS_CTRL_GCK_W::new(self, 1)
    }
}
#[doc = "\n\nYou can [`read`](crate::Reg::read) this register and get [`core_gck_cfg::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`core_gck_cfg::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct CORE_GCK_CFG_SPEC;
impl crate::RegisterSpec for CORE_GCK_CFG_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`core_gck_cfg::R`](R) reader structure"]
impl crate::Readable for CORE_GCK_CFG_SPEC {}
#[doc = "`write(|w| ..)` method takes [`core_gck_cfg::W`](W) writer structure"]
impl crate::Writable for CORE_GCK_CFG_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets CORE_GCK_CFG to value 0"]
impl crate::Resettable for CORE_GCK_CFG_SPEC {}
