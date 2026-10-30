#[doc = "Register `FLOW_CONF` reader"]
pub type R = crate::R<FLOW_CONF_SPEC>;
#[doc = "Register `FLOW_CONF` writer"]
pub type W = crate::W<FLOW_CONF_SPEC>;
#[doc = "Field `SW_FLOW_CON_EN` reader - Set this bit to enable software flow control. It is used with register sw_xon or sw_xoff."]
pub type SW_FLOW_CON_EN_R = crate::BitReader;
#[doc = "Field `SW_FLOW_CON_EN` writer - Set this bit to enable software flow control. It is used with register sw_xon or sw_xoff."]
pub type SW_FLOW_CON_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `XONOFF_DEL` reader - Set this bit to remove flow control char from the received data."]
pub type XONOFF_DEL_R = crate::BitReader;
#[doc = "Field `XONOFF_DEL` writer - Set this bit to remove flow control char from the received data."]
pub type XONOFF_DEL_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `FORCE_XON` reader - Set this bit to enable the transmitter to go on sending data."]
pub type FORCE_XON_R = crate::BitReader;
#[doc = "Field `FORCE_XON` writer - Set this bit to enable the transmitter to go on sending data."]
pub type FORCE_XON_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `FORCE_XOFF` reader - Set this bit to stop the transmitter from sending data."]
pub type FORCE_XOFF_R = crate::BitReader;
#[doc = "Field `FORCE_XOFF` writer - Set this bit to stop the transmitter from sending data."]
pub type FORCE_XOFF_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SEND_XON` reader - Set this bit to send Xon char. It is cleared by hardware automatically."]
pub type SEND_XON_R = crate::BitReader;
#[doc = "Field `SEND_XON` writer - Set this bit to send Xon char. It is cleared by hardware automatically."]
pub type SEND_XON_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SEND_XOFF` reader - Set this bit to send Xoff char. It is cleared by hardware automatically."]
pub type SEND_XOFF_R = crate::BitReader;
#[doc = "Field `SEND_XOFF` writer - Set this bit to send Xoff char. It is cleared by hardware automatically."]
pub type SEND_XOFF_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 0 - Set this bit to enable software flow control. It is used with register sw_xon or sw_xoff."]
    #[inline(always)]
    pub fn sw_flow_con_en(&self) -> SW_FLOW_CON_EN_R {
        SW_FLOW_CON_EN_R::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - Set this bit to remove flow control char from the received data."]
    #[inline(always)]
    pub fn xonoff_del(&self) -> XONOFF_DEL_R {
        XONOFF_DEL_R::new(((self.bits >> 1) & 1) != 0)
    }
    #[doc = "Bit 2 - Set this bit to enable the transmitter to go on sending data."]
    #[inline(always)]
    pub fn force_xon(&self) -> FORCE_XON_R {
        FORCE_XON_R::new(((self.bits >> 2) & 1) != 0)
    }
    #[doc = "Bit 3 - Set this bit to stop the transmitter from sending data."]
    #[inline(always)]
    pub fn force_xoff(&self) -> FORCE_XOFF_R {
        FORCE_XOFF_R::new(((self.bits >> 3) & 1) != 0)
    }
    #[doc = "Bit 4 - Set this bit to send Xon char. It is cleared by hardware automatically."]
    #[inline(always)]
    pub fn send_xon(&self) -> SEND_XON_R {
        SEND_XON_R::new(((self.bits >> 4) & 1) != 0)
    }
    #[doc = "Bit 5 - Set this bit to send Xoff char. It is cleared by hardware automatically."]
    #[inline(always)]
    pub fn send_xoff(&self) -> SEND_XOFF_R {
        SEND_XOFF_R::new(((self.bits >> 5) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("FLOW_CONF")
            .field("sw_flow_con_en", &self.sw_flow_con_en())
            .field("xonoff_del", &self.xonoff_del())
            .field("force_xon", &self.force_xon())
            .field("force_xoff", &self.force_xoff())
            .field("send_xon", &self.send_xon())
            .field("send_xoff", &self.send_xoff())
            .finish()
    }
}
impl W {
    #[doc = "Bit 0 - Set this bit to enable software flow control. It is used with register sw_xon or sw_xoff."]
    #[inline(always)]
    pub fn sw_flow_con_en(&mut self) -> SW_FLOW_CON_EN_W<'_, FLOW_CONF_SPEC> {
        SW_FLOW_CON_EN_W::new(self, 0)
    }
    #[doc = "Bit 1 - Set this bit to remove flow control char from the received data."]
    #[inline(always)]
    pub fn xonoff_del(&mut self) -> XONOFF_DEL_W<'_, FLOW_CONF_SPEC> {
        XONOFF_DEL_W::new(self, 1)
    }
    #[doc = "Bit 2 - Set this bit to enable the transmitter to go on sending data."]
    #[inline(always)]
    pub fn force_xon(&mut self) -> FORCE_XON_W<'_, FLOW_CONF_SPEC> {
        FORCE_XON_W::new(self, 2)
    }
    #[doc = "Bit 3 - Set this bit to stop the transmitter from sending data."]
    #[inline(always)]
    pub fn force_xoff(&mut self) -> FORCE_XOFF_W<'_, FLOW_CONF_SPEC> {
        FORCE_XOFF_W::new(self, 3)
    }
    #[doc = "Bit 4 - Set this bit to send Xon char. It is cleared by hardware automatically."]
    #[inline(always)]
    pub fn send_xon(&mut self) -> SEND_XON_W<'_, FLOW_CONF_SPEC> {
        SEND_XON_W::new(self, 4)
    }
    #[doc = "Bit 5 - Set this bit to send Xoff char. It is cleared by hardware automatically."]
    #[inline(always)]
    pub fn send_xoff(&mut self) -> SEND_XOFF_W<'_, FLOW_CONF_SPEC> {
        SEND_XOFF_W::new(self, 5)
    }
}
#[doc = "Software flow-control configuration\n\nYou can [`read`](crate::Reg::read) this register and get [`flow_conf::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`flow_conf::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct FLOW_CONF_SPEC;
impl crate::RegisterSpec for FLOW_CONF_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`flow_conf::R`](R) reader structure"]
impl crate::Readable for FLOW_CONF_SPEC {}
#[doc = "`write(|w| ..)` method takes [`flow_conf::W`](W) writer structure"]
impl crate::Writable for FLOW_CONF_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets FLOW_CONF to value 0"]
impl crate::Resettable for FLOW_CONF_SPEC {}
