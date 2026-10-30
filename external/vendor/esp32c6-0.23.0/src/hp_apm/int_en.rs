#[doc = "Register `INT_EN` reader"]
pub type R = crate::R<INT_EN_SPEC>;
#[doc = "Register `INT_EN` writer"]
pub type W = crate::W<INT_EN_SPEC>;
#[doc = "Field `M_APM(0-3)` reader - APM M%s interrupt enable"]
pub type M_APM_R = crate::BitReader;
#[doc = "Field `M_APM(0-3)` writer - APM M%s interrupt enable"]
pub type M_APM_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "APM M(0-3) interrupt enable"]
    #[doc = ""]
    #[doc = "<div class=\"warning\">`n` is number of field in register. `n == 0` corresponds to `M0_APM` field.</div>"]
    #[inline(always)]
    pub fn m_apm(&self, n: u8) -> M_APM_R {
        #[allow(clippy::no_effect)]
        [(); 4][n as usize];
        M_APM_R::new(((self.bits >> n) & 1) != 0)
    }
    #[doc = "Iterator for array of:"]
    #[doc = "APM M(0-3) interrupt enable"]
    #[inline(always)]
    pub fn m_apm_iter(&self) -> impl Iterator<Item = M_APM_R> + '_ {
        (0..4).map(move |n| M_APM_R::new(((self.bits >> n) & 1) != 0))
    }
    #[doc = "Bit 0 - APM M0 interrupt enable"]
    #[inline(always)]
    pub fn m0_apm(&self) -> M_APM_R {
        M_APM_R::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - APM M1 interrupt enable"]
    #[inline(always)]
    pub fn m1_apm(&self) -> M_APM_R {
        M_APM_R::new(((self.bits >> 1) & 1) != 0)
    }
    #[doc = "Bit 2 - APM M2 interrupt enable"]
    #[inline(always)]
    pub fn m2_apm(&self) -> M_APM_R {
        M_APM_R::new(((self.bits >> 2) & 1) != 0)
    }
    #[doc = "Bit 3 - APM M3 interrupt enable"]
    #[inline(always)]
    pub fn m3_apm(&self) -> M_APM_R {
        M_APM_R::new(((self.bits >> 3) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("INT_EN")
            .field("m0_apm", &self.m0_apm())
            .field("m1_apm", &self.m1_apm())
            .field("m2_apm", &self.m2_apm())
            .field("m3_apm", &self.m3_apm())
            .finish()
    }
}
impl W {
    #[doc = "APM M(0-3) interrupt enable"]
    #[doc = ""]
    #[doc = "<div class=\"warning\">`n` is number of field in register. `n == 0` corresponds to `M0_APM` field.</div>"]
    #[inline(always)]
    pub fn m_apm(&mut self, n: u8) -> M_APM_W<'_, INT_EN_SPEC> {
        #[allow(clippy::no_effect)]
        [(); 4][n as usize];
        M_APM_W::new(self, n)
    }
    #[doc = "Bit 0 - APM M0 interrupt enable"]
    #[inline(always)]
    pub fn m0_apm(&mut self) -> M_APM_W<'_, INT_EN_SPEC> {
        M_APM_W::new(self, 0)
    }
    #[doc = "Bit 1 - APM M1 interrupt enable"]
    #[inline(always)]
    pub fn m1_apm(&mut self) -> M_APM_W<'_, INT_EN_SPEC> {
        M_APM_W::new(self, 1)
    }
    #[doc = "Bit 2 - APM M2 interrupt enable"]
    #[inline(always)]
    pub fn m2_apm(&mut self) -> M_APM_W<'_, INT_EN_SPEC> {
        M_APM_W::new(self, 2)
    }
    #[doc = "Bit 3 - APM M3 interrupt enable"]
    #[inline(always)]
    pub fn m3_apm(&mut self) -> M_APM_W<'_, INT_EN_SPEC> {
        M_APM_W::new(self, 3)
    }
}
#[doc = "APM interrupt enable register\n\nYou can [`read`](crate::Reg::read) this register and get [`int_en::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`int_en::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct INT_EN_SPEC;
impl crate::RegisterSpec for INT_EN_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`int_en::R`](R) reader structure"]
impl crate::Readable for INT_EN_SPEC {}
#[doc = "`write(|w| ..)` method takes [`int_en::W`](W) writer structure"]
impl crate::Writable for INT_EN_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets INT_EN to value 0"]
impl crate::Resettable for INT_EN_SPEC {}
