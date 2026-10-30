#[doc = "Register `RD_TIM_CONF` reader"]
pub type R = crate::R<RD_TIM_CONF_SPEC>;
#[doc = "Register `RD_TIM_CONF` writer"]
pub type W = crate::W<RD_TIM_CONF_SPEC>;
#[doc = "Field `THR_A` reader - Configures the read hold time."]
pub type THR_A_R = crate::FieldReader;
#[doc = "Field `THR_A` writer - Configures the read hold time."]
pub type THR_A_W<'a, REG> = crate::FieldWriter<'a, REG, 8>;
#[doc = "Field `TRD` reader - Configures the read time."]
pub type TRD_R = crate::FieldReader;
#[doc = "Field `TRD` writer - Configures the read time."]
pub type TRD_W<'a, REG> = crate::FieldWriter<'a, REG, 8>;
#[doc = "Field `TSUR_A` reader - Configures the read setup time."]
pub type TSUR_A_R = crate::FieldReader;
#[doc = "Field `TSUR_A` writer - Configures the read setup time."]
pub type TSUR_A_W<'a, REG> = crate::FieldWriter<'a, REG, 8>;
#[doc = "Field `READ_INIT_NUM` reader - Configures the waiting time of reading eFuse memory."]
pub type READ_INIT_NUM_R = crate::FieldReader;
#[doc = "Field `READ_INIT_NUM` writer - Configures the waiting time of reading eFuse memory."]
pub type READ_INIT_NUM_W<'a, REG> = crate::FieldWriter<'a, REG, 8>;
impl R {
    #[doc = "Bits 0:7 - Configures the read hold time."]
    #[inline(always)]
    pub fn thr_a(&self) -> THR_A_R {
        THR_A_R::new((self.bits & 0xff) as u8)
    }
    #[doc = "Bits 8:15 - Configures the read time."]
    #[inline(always)]
    pub fn trd(&self) -> TRD_R {
        TRD_R::new(((self.bits >> 8) & 0xff) as u8)
    }
    #[doc = "Bits 16:23 - Configures the read setup time."]
    #[inline(always)]
    pub fn tsur_a(&self) -> TSUR_A_R {
        TSUR_A_R::new(((self.bits >> 16) & 0xff) as u8)
    }
    #[doc = "Bits 24:31 - Configures the waiting time of reading eFuse memory."]
    #[inline(always)]
    pub fn read_init_num(&self) -> READ_INIT_NUM_R {
        READ_INIT_NUM_R::new(((self.bits >> 24) & 0xff) as u8)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("RD_TIM_CONF")
            .field("thr_a", &self.thr_a())
            .field("trd", &self.trd())
            .field("tsur_a", &self.tsur_a())
            .field("read_init_num", &self.read_init_num())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:7 - Configures the read hold time."]
    #[inline(always)]
    pub fn thr_a(&mut self) -> THR_A_W<'_, RD_TIM_CONF_SPEC> {
        THR_A_W::new(self, 0)
    }
    #[doc = "Bits 8:15 - Configures the read time."]
    #[inline(always)]
    pub fn trd(&mut self) -> TRD_W<'_, RD_TIM_CONF_SPEC> {
        TRD_W::new(self, 8)
    }
    #[doc = "Bits 16:23 - Configures the read setup time."]
    #[inline(always)]
    pub fn tsur_a(&mut self) -> TSUR_A_W<'_, RD_TIM_CONF_SPEC> {
        TSUR_A_W::new(self, 16)
    }
    #[doc = "Bits 24:31 - Configures the waiting time of reading eFuse memory."]
    #[inline(always)]
    pub fn read_init_num(&mut self) -> READ_INIT_NUM_W<'_, RD_TIM_CONF_SPEC> {
        READ_INIT_NUM_W::new(self, 24)
    }
}
#[doc = "Configures read timing parameters.\n\nYou can [`read`](crate::Reg::read) this register and get [`rd_tim_conf::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`rd_tim_conf::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct RD_TIM_CONF_SPEC;
impl crate::RegisterSpec for RD_TIM_CONF_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`rd_tim_conf::R`](R) reader structure"]
impl crate::Readable for RD_TIM_CONF_SPEC {}
#[doc = "`write(|w| ..)` method takes [`rd_tim_conf::W`](W) writer structure"]
impl crate::Writable for RD_TIM_CONF_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets RD_TIM_CONF to value 0x1201_0201"]
impl crate::Resettable for RD_TIM_CONF_SPEC {
    const RESET_VALUE: u32 = 0x1201_0201;
}
