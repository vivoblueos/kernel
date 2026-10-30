#[doc = "Register `TOUT_CONF` reader"]
pub type R = crate::R<TOUT_CONF_SPEC>;
#[doc = "Register `TOUT_CONF` writer"]
pub type W = crate::W<TOUT_CONF_SPEC>;
#[doc = "Field `RX_TOUT_EN` reader - This is the enble bit for uart receiver's timeout function."]
pub type RX_TOUT_EN_R = crate::BitReader;
#[doc = "Field `RX_TOUT_EN` writer - This is the enble bit for uart receiver's timeout function."]
pub type RX_TOUT_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `RX_TOUT_FLOW_DIS` reader - Set this bit to stop accumulating idle_cnt when hardware flow control works."]
pub type RX_TOUT_FLOW_DIS_R = crate::BitReader;
#[doc = "Field `RX_TOUT_FLOW_DIS` writer - Set this bit to stop accumulating idle_cnt when hardware flow control works."]
pub type RX_TOUT_FLOW_DIS_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `RX_TOUT_THRHD` reader - This register is used to configure the threshold time that receiver takes to receive one byte. The rxfifo_tout_int interrupt will be trigger when the receiver takes more time to receive one byte with rx_tout_en set to 1."]
pub type RX_TOUT_THRHD_R = crate::FieldReader<u16>;
#[doc = "Field `RX_TOUT_THRHD` writer - This register is used to configure the threshold time that receiver takes to receive one byte. The rxfifo_tout_int interrupt will be trigger when the receiver takes more time to receive one byte with rx_tout_en set to 1."]
pub type RX_TOUT_THRHD_W<'a, REG> = crate::FieldWriter<'a, REG, 10, u16>;
impl R {
    #[doc = "Bit 0 - This is the enble bit for uart receiver's timeout function."]
    #[inline(always)]
    pub fn rx_tout_en(&self) -> RX_TOUT_EN_R {
        RX_TOUT_EN_R::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - Set this bit to stop accumulating idle_cnt when hardware flow control works."]
    #[inline(always)]
    pub fn rx_tout_flow_dis(&self) -> RX_TOUT_FLOW_DIS_R {
        RX_TOUT_FLOW_DIS_R::new(((self.bits >> 1) & 1) != 0)
    }
    #[doc = "Bits 2:11 - This register is used to configure the threshold time that receiver takes to receive one byte. The rxfifo_tout_int interrupt will be trigger when the receiver takes more time to receive one byte with rx_tout_en set to 1."]
    #[inline(always)]
    pub fn rx_tout_thrhd(&self) -> RX_TOUT_THRHD_R {
        RX_TOUT_THRHD_R::new(((self.bits >> 2) & 0x03ff) as u16)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("TOUT_CONF")
            .field("rx_tout_en", &self.rx_tout_en())
            .field("rx_tout_flow_dis", &self.rx_tout_flow_dis())
            .field("rx_tout_thrhd", &self.rx_tout_thrhd())
            .finish()
    }
}
impl W {
    #[doc = "Bit 0 - This is the enble bit for uart receiver's timeout function."]
    #[inline(always)]
    pub fn rx_tout_en(&mut self) -> RX_TOUT_EN_W<'_, TOUT_CONF_SPEC> {
        RX_TOUT_EN_W::new(self, 0)
    }
    #[doc = "Bit 1 - Set this bit to stop accumulating idle_cnt when hardware flow control works."]
    #[inline(always)]
    pub fn rx_tout_flow_dis(&mut self) -> RX_TOUT_FLOW_DIS_W<'_, TOUT_CONF_SPEC> {
        RX_TOUT_FLOW_DIS_W::new(self, 1)
    }
    #[doc = "Bits 2:11 - This register is used to configure the threshold time that receiver takes to receive one byte. The rxfifo_tout_int interrupt will be trigger when the receiver takes more time to receive one byte with rx_tout_en set to 1."]
    #[inline(always)]
    pub fn rx_tout_thrhd(&mut self) -> RX_TOUT_THRHD_W<'_, TOUT_CONF_SPEC> {
        RX_TOUT_THRHD_W::new(self, 2)
    }
}
#[doc = "UART threshold and allocation configuration\n\nYou can [`read`](crate::Reg::read) this register and get [`tout_conf::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`tout_conf::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct TOUT_CONF_SPEC;
impl crate::RegisterSpec for TOUT_CONF_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`tout_conf::R`](R) reader structure"]
impl crate::Readable for TOUT_CONF_SPEC {}
#[doc = "`write(|w| ..)` method takes [`tout_conf::W`](W) writer structure"]
impl crate::Writable for TOUT_CONF_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets TOUT_CONF to value 0x28"]
impl crate::Resettable for TOUT_CONF_SPEC {
    const RESET_VALUE: u32 = 0x28;
}
