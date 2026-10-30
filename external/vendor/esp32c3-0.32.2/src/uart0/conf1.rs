#[doc = "Register `CONF1` reader"]
pub type R = crate::R<CONF1_SPEC>;
#[doc = "Register `CONF1` writer"]
pub type W = crate::W<CONF1_SPEC>;
#[doc = "Field `RXFIFO_FULL_THRHD` reader - It will produce rxfifo_full_int interrupt when receiver receives more data than this register value."]
pub type RXFIFO_FULL_THRHD_R = crate::FieldReader<u16>;
#[doc = "Field `RXFIFO_FULL_THRHD` writer - It will produce rxfifo_full_int interrupt when receiver receives more data than this register value."]
pub type RXFIFO_FULL_THRHD_W<'a, REG> = crate::FieldWriter<'a, REG, 9, u16>;
#[doc = "Field `TXFIFO_EMPTY_THRHD` reader - It will produce txfifo_empty_int interrupt when the data amount in Tx-FIFO is less than this register value."]
pub type TXFIFO_EMPTY_THRHD_R = crate::FieldReader<u16>;
#[doc = "Field `TXFIFO_EMPTY_THRHD` writer - It will produce txfifo_empty_int interrupt when the data amount in Tx-FIFO is less than this register value."]
pub type TXFIFO_EMPTY_THRHD_W<'a, REG> = crate::FieldWriter<'a, REG, 9, u16>;
#[doc = "Field `DIS_RX_DAT_OVF` reader - Disable UART Rx data overflow detect."]
pub type DIS_RX_DAT_OVF_R = crate::BitReader;
#[doc = "Field `DIS_RX_DAT_OVF` writer - Disable UART Rx data overflow detect."]
pub type DIS_RX_DAT_OVF_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `RX_TOUT_FLOW_DIS` reader - Set this bit to stop accumulating idle_cnt when hardware flow control works."]
pub type RX_TOUT_FLOW_DIS_R = crate::BitReader;
#[doc = "Field `RX_TOUT_FLOW_DIS` writer - Set this bit to stop accumulating idle_cnt when hardware flow control works."]
pub type RX_TOUT_FLOW_DIS_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `RX_FLOW_EN` reader - This is the flow enable bit for UART receiver."]
pub type RX_FLOW_EN_R = crate::BitReader;
#[doc = "Field `RX_FLOW_EN` writer - This is the flow enable bit for UART receiver."]
pub type RX_FLOW_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `RX_TOUT_EN` reader - This is the enble bit for uart receiver's timeout function."]
pub type RX_TOUT_EN_R = crate::BitReader;
#[doc = "Field `RX_TOUT_EN` writer - This is the enble bit for uart receiver's timeout function."]
pub type RX_TOUT_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bits 0:8 - It will produce rxfifo_full_int interrupt when receiver receives more data than this register value."]
    #[inline(always)]
    pub fn rxfifo_full_thrhd(&self) -> RXFIFO_FULL_THRHD_R {
        RXFIFO_FULL_THRHD_R::new((self.bits & 0x01ff) as u16)
    }
    #[doc = "Bits 9:17 - It will produce txfifo_empty_int interrupt when the data amount in Tx-FIFO is less than this register value."]
    #[inline(always)]
    pub fn txfifo_empty_thrhd(&self) -> TXFIFO_EMPTY_THRHD_R {
        TXFIFO_EMPTY_THRHD_R::new(((self.bits >> 9) & 0x01ff) as u16)
    }
    #[doc = "Bit 18 - Disable UART Rx data overflow detect."]
    #[inline(always)]
    pub fn dis_rx_dat_ovf(&self) -> DIS_RX_DAT_OVF_R {
        DIS_RX_DAT_OVF_R::new(((self.bits >> 18) & 1) != 0)
    }
    #[doc = "Bit 19 - Set this bit to stop accumulating idle_cnt when hardware flow control works."]
    #[inline(always)]
    pub fn rx_tout_flow_dis(&self) -> RX_TOUT_FLOW_DIS_R {
        RX_TOUT_FLOW_DIS_R::new(((self.bits >> 19) & 1) != 0)
    }
    #[doc = "Bit 20 - This is the flow enable bit for UART receiver."]
    #[inline(always)]
    pub fn rx_flow_en(&self) -> RX_FLOW_EN_R {
        RX_FLOW_EN_R::new(((self.bits >> 20) & 1) != 0)
    }
    #[doc = "Bit 21 - This is the enble bit for uart receiver's timeout function."]
    #[inline(always)]
    pub fn rx_tout_en(&self) -> RX_TOUT_EN_R {
        RX_TOUT_EN_R::new(((self.bits >> 21) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("CONF1")
            .field("rxfifo_full_thrhd", &self.rxfifo_full_thrhd())
            .field("txfifo_empty_thrhd", &self.txfifo_empty_thrhd())
            .field("dis_rx_dat_ovf", &self.dis_rx_dat_ovf())
            .field("rx_tout_flow_dis", &self.rx_tout_flow_dis())
            .field("rx_flow_en", &self.rx_flow_en())
            .field("rx_tout_en", &self.rx_tout_en())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:8 - It will produce rxfifo_full_int interrupt when receiver receives more data than this register value."]
    #[inline(always)]
    pub fn rxfifo_full_thrhd(&mut self) -> RXFIFO_FULL_THRHD_W<'_, CONF1_SPEC> {
        RXFIFO_FULL_THRHD_W::new(self, 0)
    }
    #[doc = "Bits 9:17 - It will produce txfifo_empty_int interrupt when the data amount in Tx-FIFO is less than this register value."]
    #[inline(always)]
    pub fn txfifo_empty_thrhd(&mut self) -> TXFIFO_EMPTY_THRHD_W<'_, CONF1_SPEC> {
        TXFIFO_EMPTY_THRHD_W::new(self, 9)
    }
    #[doc = "Bit 18 - Disable UART Rx data overflow detect."]
    #[inline(always)]
    pub fn dis_rx_dat_ovf(&mut self) -> DIS_RX_DAT_OVF_W<'_, CONF1_SPEC> {
        DIS_RX_DAT_OVF_W::new(self, 18)
    }
    #[doc = "Bit 19 - Set this bit to stop accumulating idle_cnt when hardware flow control works."]
    #[inline(always)]
    pub fn rx_tout_flow_dis(&mut self) -> RX_TOUT_FLOW_DIS_W<'_, CONF1_SPEC> {
        RX_TOUT_FLOW_DIS_W::new(self, 19)
    }
    #[doc = "Bit 20 - This is the flow enable bit for UART receiver."]
    #[inline(always)]
    pub fn rx_flow_en(&mut self) -> RX_FLOW_EN_W<'_, CONF1_SPEC> {
        RX_FLOW_EN_W::new(self, 20)
    }
    #[doc = "Bit 21 - This is the enble bit for uart receiver's timeout function."]
    #[inline(always)]
    pub fn rx_tout_en(&mut self) -> RX_TOUT_EN_W<'_, CONF1_SPEC> {
        RX_TOUT_EN_W::new(self, 21)
    }
}
#[doc = "Configuration register 1\n\nYou can [`read`](crate::Reg::read) this register and get [`conf1::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`conf1::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct CONF1_SPEC;
impl crate::RegisterSpec for CONF1_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`conf1::R`](R) reader structure"]
impl crate::Readable for CONF1_SPEC {}
#[doc = "`write(|w| ..)` method takes [`conf1::W`](W) writer structure"]
impl crate::Writable for CONF1_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets CONF1 to value 0xc060"]
impl crate::Resettable for CONF1_SPEC {
    const RESET_VALUE: u32 = 0xc060;
}
