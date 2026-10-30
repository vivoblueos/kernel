#[doc = "Register `AT_CMD_GAPTOUT` reader"]
pub type R = crate::R<AT_CMD_GAPTOUT_SPEC>;
#[doc = "Register `AT_CMD_GAPTOUT` writer"]
pub type W = crate::W<AT_CMD_GAPTOUT_SPEC>;
#[doc = "Field `RX_GAP_TOUT` reader - This register is used to configure the duration time between the at_cmd chars."]
pub type RX_GAP_TOUT_R = crate::FieldReader<u16>;
#[doc = "Field `RX_GAP_TOUT` writer - This register is used to configure the duration time between the at_cmd chars."]
pub type RX_GAP_TOUT_W<'a, REG> = crate::FieldWriter<'a, REG, 16, u16>;
impl R {
    #[doc = "Bits 0:15 - This register is used to configure the duration time between the at_cmd chars."]
    #[inline(always)]
    pub fn rx_gap_tout(&self) -> RX_GAP_TOUT_R {
        RX_GAP_TOUT_R::new((self.bits & 0xffff) as u16)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("AT_CMD_GAPTOUT")
            .field("rx_gap_tout", &self.rx_gap_tout())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:15 - This register is used to configure the duration time between the at_cmd chars."]
    #[inline(always)]
    pub fn rx_gap_tout(&mut self) -> RX_GAP_TOUT_W<'_, AT_CMD_GAPTOUT_SPEC> {
        RX_GAP_TOUT_W::new(self, 0)
    }
}
#[doc = "Timeout configuration\n\nYou can [`read`](crate::Reg::read) this register and get [`at_cmd_gaptout::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`at_cmd_gaptout::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct AT_CMD_GAPTOUT_SPEC;
impl crate::RegisterSpec for AT_CMD_GAPTOUT_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`at_cmd_gaptout::R`](R) reader structure"]
impl crate::Readable for AT_CMD_GAPTOUT_SPEC {}
#[doc = "`write(|w| ..)` method takes [`at_cmd_gaptout::W`](W) writer structure"]
impl crate::Writable for AT_CMD_GAPTOUT_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets AT_CMD_GAPTOUT to value 0x0b"]
impl crate::Resettable for AT_CMD_GAPTOUT_SPEC {
    const RESET_VALUE: u32 = 0x0b;
}
