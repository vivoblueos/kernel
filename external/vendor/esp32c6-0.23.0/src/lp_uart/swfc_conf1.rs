#[doc = "Register `SWFC_CONF1` reader"]
pub type R = crate::R<SWFC_CONF1_SPEC>;
#[doc = "Register `SWFC_CONF1` writer"]
pub type W = crate::W<SWFC_CONF1_SPEC>;
#[doc = "Field `XON_THRESHOLD` reader - When the data amount in Rx-FIFO is less than this register value with uart_sw_flow_con_en set to 1 it will send a Xon char."]
pub type XON_THRESHOLD_R = crate::FieldReader;
#[doc = "Field `XON_THRESHOLD` writer - When the data amount in Rx-FIFO is less than this register value with uart_sw_flow_con_en set to 1 it will send a Xon char."]
pub type XON_THRESHOLD_W<'a, REG> = crate::FieldWriter<'a, REG, 5>;
#[doc = "Field `XOFF_THRESHOLD` reader - When the data amount in Rx-FIFO is more than this register value with uart_sw_flow_con_en set to 1 it will send a Xoff char."]
pub type XOFF_THRESHOLD_R = crate::FieldReader;
#[doc = "Field `XOFF_THRESHOLD` writer - When the data amount in Rx-FIFO is more than this register value with uart_sw_flow_con_en set to 1 it will send a Xoff char."]
pub type XOFF_THRESHOLD_W<'a, REG> = crate::FieldWriter<'a, REG, 5>;
impl R {
    #[doc = "Bits 3:7 - When the data amount in Rx-FIFO is less than this register value with uart_sw_flow_con_en set to 1 it will send a Xon char."]
    #[inline(always)]
    pub fn xon_threshold(&self) -> XON_THRESHOLD_R {
        XON_THRESHOLD_R::new(((self.bits >> 3) & 0x1f) as u8)
    }
    #[doc = "Bits 11:15 - When the data amount in Rx-FIFO is more than this register value with uart_sw_flow_con_en set to 1 it will send a Xoff char."]
    #[inline(always)]
    pub fn xoff_threshold(&self) -> XOFF_THRESHOLD_R {
        XOFF_THRESHOLD_R::new(((self.bits >> 11) & 0x1f) as u8)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("SWFC_CONF1")
            .field("xon_threshold", &self.xon_threshold())
            .field("xoff_threshold", &self.xoff_threshold())
            .finish()
    }
}
impl W {
    #[doc = "Bits 3:7 - When the data amount in Rx-FIFO is less than this register value with uart_sw_flow_con_en set to 1 it will send a Xon char."]
    #[inline(always)]
    pub fn xon_threshold(&mut self) -> XON_THRESHOLD_W<'_, SWFC_CONF1_SPEC> {
        XON_THRESHOLD_W::new(self, 3)
    }
    #[doc = "Bits 11:15 - When the data amount in Rx-FIFO is more than this register value with uart_sw_flow_con_en set to 1 it will send a Xoff char."]
    #[inline(always)]
    pub fn xoff_threshold(&mut self) -> XOFF_THRESHOLD_W<'_, SWFC_CONF1_SPEC> {
        XOFF_THRESHOLD_W::new(self, 11)
    }
}
#[doc = "Software flow-control character configuration\n\nYou can [`read`](crate::Reg::read) this register and get [`swfc_conf1::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`swfc_conf1::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct SWFC_CONF1_SPEC;
impl crate::RegisterSpec for SWFC_CONF1_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`swfc_conf1::R`](R) reader structure"]
impl crate::Readable for SWFC_CONF1_SPEC {}
#[doc = "`write(|w| ..)` method takes [`swfc_conf1::W`](W) writer structure"]
impl crate::Writable for SWFC_CONF1_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets SWFC_CONF1 to value 0x6000"]
impl crate::Resettable for SWFC_CONF1_SPEC {
    const RESET_VALUE: u32 = 0x6000;
}
