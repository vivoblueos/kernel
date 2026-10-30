#[doc = "Register `CONF2` reader"]
pub type R = crate::R<CONF2_SPEC>;
#[doc = "Register `CONF2` writer"]
pub type W = crate::W<CONF2_SPEC>;
#[doc = "Field `CNT_H_LIM` reader - This register is used to configure the thr_h_lim value for unit %s."]
pub type CNT_H_LIM_R = crate::FieldReader<u16>;
#[doc = "Field `CNT_H_LIM` writer - This register is used to configure the thr_h_lim value for unit %s."]
pub type CNT_H_LIM_W<'a, REG> = crate::FieldWriter<'a, REG, 16, u16>;
#[doc = "Field `CNT_L_LIM` reader - This register is used to configure the thr_l_lim value for unit %s."]
pub type CNT_L_LIM_R = crate::FieldReader<u16>;
#[doc = "Field `CNT_L_LIM` writer - This register is used to configure the thr_l_lim value for unit %s."]
pub type CNT_L_LIM_W<'a, REG> = crate::FieldWriter<'a, REG, 16, u16>;
impl R {
    #[doc = "Bits 0:15 - This register is used to configure the thr_h_lim value for unit %s."]
    #[inline(always)]
    pub fn cnt_h_lim(&self) -> CNT_H_LIM_R {
        CNT_H_LIM_R::new((self.bits & 0xffff) as u16)
    }
    #[doc = "Bits 16:31 - This register is used to configure the thr_l_lim value for unit %s."]
    #[inline(always)]
    pub fn cnt_l_lim(&self) -> CNT_L_LIM_R {
        CNT_L_LIM_R::new(((self.bits >> 16) & 0xffff) as u16)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("CONF2")
            .field("cnt_h_lim", &self.cnt_h_lim())
            .field("cnt_l_lim", &self.cnt_l_lim())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:15 - This register is used to configure the thr_h_lim value for unit %s."]
    #[inline(always)]
    pub fn cnt_h_lim(&mut self) -> CNT_H_LIM_W<'_, CONF2_SPEC> {
        CNT_H_LIM_W::new(self, 0)
    }
    #[doc = "Bits 16:31 - This register is used to configure the thr_l_lim value for unit %s."]
    #[inline(always)]
    pub fn cnt_l_lim(&mut self) -> CNT_L_LIM_W<'_, CONF2_SPEC> {
        CNT_L_LIM_W::new(self, 16)
    }
}
#[doc = "Configuration register 2 for unit 0\n\nYou can [`read`](crate::Reg::read) this register and get [`conf2::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`conf2::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct CONF2_SPEC;
impl crate::RegisterSpec for CONF2_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`conf2::R`](R) reader structure"]
impl crate::Readable for CONF2_SPEC {}
#[doc = "`write(|w| ..)` method takes [`conf2::W`](W) writer structure"]
impl crate::Writable for CONF2_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets CONF2 to value 0"]
impl crate::Resettable for CONF2_SPEC {}
