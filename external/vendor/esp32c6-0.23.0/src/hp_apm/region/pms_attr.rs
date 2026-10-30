#[doc = "Register `PMS_ATTR` reader"]
pub type R = crate::R<PMS_ATTR_SPEC>;
#[doc = "Register `PMS_ATTR` writer"]
pub type W = crate::W<PMS_ATTR_SPEC>;
#[doc = "Field `R_PMS_X(0-2)` reader - Region execute authority in REE_MODE%s"]
pub type R_PMS_X_R = crate::BitReader;
#[doc = "Field `R_PMS_X(0-2)` writer - Region execute authority in REE_MODE%s"]
pub type R_PMS_X_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `R_PMS_W(0-2)` reader - Region write authority in REE_MODE%s"]
pub type R_PMS_W_R = crate::BitReader;
#[doc = "Field `R_PMS_W(0-2)` writer - Region write authority in REE_MODE%s"]
pub type R_PMS_W_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `R_PMS_R(0-2)` reader - Region read authority in REE_MODE%s"]
pub type R_PMS_R_R = crate::BitReader;
#[doc = "Field `R_PMS_R(0-2)` writer - Region read authority in REE_MODE%s"]
pub type R_PMS_R_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Region execute authority in REE_MODE(0-2)"]
    #[doc = ""]
    #[doc = "<div class=\"warning\">`n` is number of field in register. `n == 0` corresponds to `R0_PMS_X` field.</div>"]
    #[inline(always)]
    pub fn r_pms_x(&self, n: u8) -> R_PMS_X_R {
        #[allow(clippy::no_effect)]
        [(); 3][n as usize];
        R_PMS_X_R::new(((self.bits >> (n * 4)) & 1) != 0)
    }
    #[doc = "Iterator for array of:"]
    #[doc = "Region execute authority in REE_MODE(0-2)"]
    #[inline(always)]
    pub fn r_pms_x_iter(&self) -> impl Iterator<Item = R_PMS_X_R> + '_ {
        (0..3).map(move |n| R_PMS_X_R::new(((self.bits >> (n * 4)) & 1) != 0))
    }
    #[doc = "Bit 0 - Region execute authority in REE_MODE0"]
    #[inline(always)]
    pub fn r0_pms_x(&self) -> R_PMS_X_R {
        R_PMS_X_R::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 4 - Region execute authority in REE_MODE1"]
    #[inline(always)]
    pub fn r1_pms_x(&self) -> R_PMS_X_R {
        R_PMS_X_R::new(((self.bits >> 4) & 1) != 0)
    }
    #[doc = "Bit 8 - Region execute authority in REE_MODE2"]
    #[inline(always)]
    pub fn r2_pms_x(&self) -> R_PMS_X_R {
        R_PMS_X_R::new(((self.bits >> 8) & 1) != 0)
    }
    #[doc = "Region write authority in REE_MODE(0-2)"]
    #[doc = ""]
    #[doc = "<div class=\"warning\">`n` is number of field in register. `n == 0` corresponds to `R0_PMS_W` field.</div>"]
    #[inline(always)]
    pub fn r_pms_w(&self, n: u8) -> R_PMS_W_R {
        #[allow(clippy::no_effect)]
        [(); 3][n as usize];
        R_PMS_W_R::new(((self.bits >> (n * 4 + 1)) & 1) != 0)
    }
    #[doc = "Iterator for array of:"]
    #[doc = "Region write authority in REE_MODE(0-2)"]
    #[inline(always)]
    pub fn r_pms_w_iter(&self) -> impl Iterator<Item = R_PMS_W_R> + '_ {
        (0..3).map(move |n| R_PMS_W_R::new(((self.bits >> (n * 4 + 1)) & 1) != 0))
    }
    #[doc = "Bit 1 - Region write authority in REE_MODE0"]
    #[inline(always)]
    pub fn r0_pms_w(&self) -> R_PMS_W_R {
        R_PMS_W_R::new(((self.bits >> 1) & 1) != 0)
    }
    #[doc = "Bit 5 - Region write authority in REE_MODE1"]
    #[inline(always)]
    pub fn r1_pms_w(&self) -> R_PMS_W_R {
        R_PMS_W_R::new(((self.bits >> 5) & 1) != 0)
    }
    #[doc = "Bit 9 - Region write authority in REE_MODE2"]
    #[inline(always)]
    pub fn r2_pms_w(&self) -> R_PMS_W_R {
        R_PMS_W_R::new(((self.bits >> 9) & 1) != 0)
    }
    #[doc = "Region read authority in REE_MODE(0-2)"]
    #[doc = ""]
    #[doc = "<div class=\"warning\">`n` is number of field in register. `n == 0` corresponds to `R0_PMS_R` field.</div>"]
    #[inline(always)]
    pub fn r_pms_r(&self, n: u8) -> R_PMS_R_R {
        #[allow(clippy::no_effect)]
        [(); 3][n as usize];
        R_PMS_R_R::new(((self.bits >> (n * 4 + 2)) & 1) != 0)
    }
    #[doc = "Iterator for array of:"]
    #[doc = "Region read authority in REE_MODE(0-2)"]
    #[inline(always)]
    pub fn r_pms_r_iter(&self) -> impl Iterator<Item = R_PMS_R_R> + '_ {
        (0..3).map(move |n| R_PMS_R_R::new(((self.bits >> (n * 4 + 2)) & 1) != 0))
    }
    #[doc = "Bit 2 - Region read authority in REE_MODE0"]
    #[inline(always)]
    pub fn r0_pms_r(&self) -> R_PMS_R_R {
        R_PMS_R_R::new(((self.bits >> 2) & 1) != 0)
    }
    #[doc = "Bit 6 - Region read authority in REE_MODE1"]
    #[inline(always)]
    pub fn r1_pms_r(&self) -> R_PMS_R_R {
        R_PMS_R_R::new(((self.bits >> 6) & 1) != 0)
    }
    #[doc = "Bit 10 - Region read authority in REE_MODE2"]
    #[inline(always)]
    pub fn r2_pms_r(&self) -> R_PMS_R_R {
        R_PMS_R_R::new(((self.bits >> 10) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("PMS_ATTR")
            .field("r0_pms_x", &self.r0_pms_x())
            .field("r1_pms_x", &self.r1_pms_x())
            .field("r2_pms_x", &self.r2_pms_x())
            .field("r0_pms_w", &self.r0_pms_w())
            .field("r1_pms_w", &self.r1_pms_w())
            .field("r2_pms_w", &self.r2_pms_w())
            .field("r0_pms_r", &self.r0_pms_r())
            .field("r1_pms_r", &self.r1_pms_r())
            .field("r2_pms_r", &self.r2_pms_r())
            .finish()
    }
}
impl W {
    #[doc = "Region execute authority in REE_MODE(0-2)"]
    #[doc = ""]
    #[doc = "<div class=\"warning\">`n` is number of field in register. `n == 0` corresponds to `R0_PMS_X` field.</div>"]
    #[inline(always)]
    pub fn r_pms_x(&mut self, n: u8) -> R_PMS_X_W<'_, PMS_ATTR_SPEC> {
        #[allow(clippy::no_effect)]
        [(); 3][n as usize];
        R_PMS_X_W::new(self, n * 4)
    }
    #[doc = "Bit 0 - Region execute authority in REE_MODE0"]
    #[inline(always)]
    pub fn r0_pms_x(&mut self) -> R_PMS_X_W<'_, PMS_ATTR_SPEC> {
        R_PMS_X_W::new(self, 0)
    }
    #[doc = "Bit 4 - Region execute authority in REE_MODE1"]
    #[inline(always)]
    pub fn r1_pms_x(&mut self) -> R_PMS_X_W<'_, PMS_ATTR_SPEC> {
        R_PMS_X_W::new(self, 4)
    }
    #[doc = "Bit 8 - Region execute authority in REE_MODE2"]
    #[inline(always)]
    pub fn r2_pms_x(&mut self) -> R_PMS_X_W<'_, PMS_ATTR_SPEC> {
        R_PMS_X_W::new(self, 8)
    }
    #[doc = "Region write authority in REE_MODE(0-2)"]
    #[doc = ""]
    #[doc = "<div class=\"warning\">`n` is number of field in register. `n == 0` corresponds to `R0_PMS_W` field.</div>"]
    #[inline(always)]
    pub fn r_pms_w(&mut self, n: u8) -> R_PMS_W_W<'_, PMS_ATTR_SPEC> {
        #[allow(clippy::no_effect)]
        [(); 3][n as usize];
        R_PMS_W_W::new(self, n * 4 + 1)
    }
    #[doc = "Bit 1 - Region write authority in REE_MODE0"]
    #[inline(always)]
    pub fn r0_pms_w(&mut self) -> R_PMS_W_W<'_, PMS_ATTR_SPEC> {
        R_PMS_W_W::new(self, 1)
    }
    #[doc = "Bit 5 - Region write authority in REE_MODE1"]
    #[inline(always)]
    pub fn r1_pms_w(&mut self) -> R_PMS_W_W<'_, PMS_ATTR_SPEC> {
        R_PMS_W_W::new(self, 5)
    }
    #[doc = "Bit 9 - Region write authority in REE_MODE2"]
    #[inline(always)]
    pub fn r2_pms_w(&mut self) -> R_PMS_W_W<'_, PMS_ATTR_SPEC> {
        R_PMS_W_W::new(self, 9)
    }
    #[doc = "Region read authority in REE_MODE(0-2)"]
    #[doc = ""]
    #[doc = "<div class=\"warning\">`n` is number of field in register. `n == 0` corresponds to `R0_PMS_R` field.</div>"]
    #[inline(always)]
    pub fn r_pms_r(&mut self, n: u8) -> R_PMS_R_W<'_, PMS_ATTR_SPEC> {
        #[allow(clippy::no_effect)]
        [(); 3][n as usize];
        R_PMS_R_W::new(self, n * 4 + 2)
    }
    #[doc = "Bit 2 - Region read authority in REE_MODE0"]
    #[inline(always)]
    pub fn r0_pms_r(&mut self) -> R_PMS_R_W<'_, PMS_ATTR_SPEC> {
        R_PMS_R_W::new(self, 2)
    }
    #[doc = "Bit 6 - Region read authority in REE_MODE1"]
    #[inline(always)]
    pub fn r1_pms_r(&mut self) -> R_PMS_R_W<'_, PMS_ATTR_SPEC> {
        R_PMS_R_W::new(self, 6)
    }
    #[doc = "Bit 10 - Region read authority in REE_MODE2"]
    #[inline(always)]
    pub fn r2_pms_r(&mut self) -> R_PMS_R_W<'_, PMS_ATTR_SPEC> {
        R_PMS_R_W::new(self, 10)
    }
}
#[doc = "Region access authority attribute register\n\nYou can [`read`](crate::Reg::read) this register and get [`pms_attr::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`pms_attr::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct PMS_ATTR_SPEC;
impl crate::RegisterSpec for PMS_ATTR_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`pms_attr::R`](R) reader structure"]
impl crate::Readable for PMS_ATTR_SPEC {}
#[doc = "`write(|w| ..)` method takes [`pms_attr::W`](W) writer structure"]
impl crate::Writable for PMS_ATTR_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets PMS_ATTR to value 0"]
impl crate::Resettable for PMS_ATTR_SPEC {}
