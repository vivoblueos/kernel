#[doc = "Register `TICK_CONF` reader"]
pub type R = crate::R<TICK_CONF_SPEC>;
#[doc = "Register `TICK_CONF` writer"]
pub type W = crate::W<TICK_CONF_SPEC>;
#[doc = "Field `XTAL_TICK_NUM` reader - reg_xtal_tick_num"]
pub type XTAL_TICK_NUM_R = crate::FieldReader;
#[doc = "Field `XTAL_TICK_NUM` writer - reg_xtal_tick_num"]
pub type XTAL_TICK_NUM_W<'a, REG> = crate::FieldWriter<'a, REG, 8>;
#[doc = "Field `CK8M_TICK_NUM` reader - reg_ck8m_tick_num"]
pub type CK8M_TICK_NUM_R = crate::FieldReader;
#[doc = "Field `CK8M_TICK_NUM` writer - reg_ck8m_tick_num"]
pub type CK8M_TICK_NUM_W<'a, REG> = crate::FieldWriter<'a, REG, 8>;
#[doc = "Field `TICK_ENABLE` reader - reg_tick_enable"]
pub type TICK_ENABLE_R = crate::BitReader;
#[doc = "Field `TICK_ENABLE` writer - reg_tick_enable"]
pub type TICK_ENABLE_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bits 0:7 - reg_xtal_tick_num"]
    #[inline(always)]
    pub fn xtal_tick_num(&self) -> XTAL_TICK_NUM_R {
        XTAL_TICK_NUM_R::new((self.bits & 0xff) as u8)
    }
    #[doc = "Bits 8:15 - reg_ck8m_tick_num"]
    #[inline(always)]
    pub fn ck8m_tick_num(&self) -> CK8M_TICK_NUM_R {
        CK8M_TICK_NUM_R::new(((self.bits >> 8) & 0xff) as u8)
    }
    #[doc = "Bit 16 - reg_tick_enable"]
    #[inline(always)]
    pub fn tick_enable(&self) -> TICK_ENABLE_R {
        TICK_ENABLE_R::new(((self.bits >> 16) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("TICK_CONF")
            .field("xtal_tick_num", &self.xtal_tick_num())
            .field("ck8m_tick_num", &self.ck8m_tick_num())
            .field("tick_enable", &self.tick_enable())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:7 - reg_xtal_tick_num"]
    #[inline(always)]
    pub fn xtal_tick_num(&mut self) -> XTAL_TICK_NUM_W<'_, TICK_CONF_SPEC> {
        XTAL_TICK_NUM_W::new(self, 0)
    }
    #[doc = "Bits 8:15 - reg_ck8m_tick_num"]
    #[inline(always)]
    pub fn ck8m_tick_num(&mut self) -> CK8M_TICK_NUM_W<'_, TICK_CONF_SPEC> {
        CK8M_TICK_NUM_W::new(self, 8)
    }
    #[doc = "Bit 16 - reg_tick_enable"]
    #[inline(always)]
    pub fn tick_enable(&mut self) -> TICK_ENABLE_W<'_, TICK_CONF_SPEC> {
        TICK_ENABLE_W::new(self, 16)
    }
}
#[doc = "APB_CTRL_TICK_CONF_REG\n\nYou can [`read`](crate::Reg::read) this register and get [`tick_conf::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`tick_conf::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct TICK_CONF_SPEC;
impl crate::RegisterSpec for TICK_CONF_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`tick_conf::R`](R) reader structure"]
impl crate::Readable for TICK_CONF_SPEC {}
#[doc = "`write(|w| ..)` method takes [`tick_conf::W`](W) writer structure"]
impl crate::Writable for TICK_CONF_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets TICK_CONF to value 0x0001_0727"]
impl crate::Resettable for TICK_CONF_SPEC {
    const RESET_VALUE: u32 = 0x0001_0727;
}
