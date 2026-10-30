#[doc = "Register `BURST_CONF` reader"]
pub type R = crate::R<BURST_CONF_SPEC>;
#[doc = "Register `BURST_CONF` writer"]
pub type W = crate::W<BURST_CONF_SPEC>;
#[doc = "Field `BURST_CTRL` reader - ?"]
pub type BURST_CTRL_R = crate::FieldReader<u32>;
#[doc = "Field `BURST_CTRL` writer - ?"]
pub type BURST_CTRL_W<'a, REG> = crate::FieldWriter<'a, REG, 32, u32>;
impl R {
    #[doc = "Bits 0:31 - ?"]
    #[inline(always)]
    pub fn burst_ctrl(&self) -> BURST_CTRL_R {
        BURST_CTRL_R::new(self.bits)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("BURST_CONF")
            .field("burst_ctrl", &self.burst_ctrl())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:31 - ?"]
    #[inline(always)]
    pub fn burst_ctrl(&mut self) -> BURST_CTRL_W<'_, BURST_CONF_SPEC> {
        BURST_CTRL_W::new(self, 0)
    }
}
#[doc = "BURST_CONF register\n\nYou can [`read`](crate::Reg::read) this register and get [`burst_conf::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`burst_conf::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct BURST_CONF_SPEC;
impl crate::RegisterSpec for BURST_CONF_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`burst_conf::R`](R) reader structure"]
impl crate::Readable for BURST_CONF_SPEC {}
#[doc = "`write(|w| ..)` method takes [`burst_conf::W`](W) writer structure"]
impl crate::Writable for BURST_CONF_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets BURST_CONF to value 0"]
impl crate::Resettable for BURST_CONF_SPEC {}
