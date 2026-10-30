#[doc = "Register `CONF0` reader"]
pub type R = crate::R<CONF0_SPEC>;
#[doc = "Register `CONF0` writer"]
pub type W = crate::W<CONF0_SPEC>;
#[doc = "Field `TX_RST` reader - Write 1 then write 0 to this bit to reset decode state machine."]
pub type TX_RST_R = crate::BitReader;
#[doc = "Field `TX_RST` writer - Write 1 then write 0 to this bit to reset decode state machine."]
pub type TX_RST_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `RX_RST` reader - Write 1 then write 0 to this bit to reset encode state machine."]
pub type RX_RST_R = crate::BitReader;
#[doc = "Field `RX_RST` writer - Write 1 then write 0 to this bit to reset encode state machine."]
pub type RX_RST_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `UART0_CE` reader - Set this bit to link up HCI and UART0."]
pub type UART0_CE_R = crate::BitReader;
#[doc = "Field `UART0_CE` writer - Set this bit to link up HCI and UART0."]
pub type UART0_CE_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `UART1_CE` reader - Set this bit to link up HCI and UART1."]
pub type UART1_CE_R = crate::BitReader;
#[doc = "Field `UART1_CE` writer - Set this bit to link up HCI and UART1."]
pub type UART1_CE_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SEPER_EN` reader - Set this bit to separate the data frame using a special char."]
pub type SEPER_EN_R = crate::BitReader;
#[doc = "Field `SEPER_EN` writer - Set this bit to separate the data frame using a special char."]
pub type SEPER_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `HEAD_EN` reader - Set this bit to encode the data packet with a formatting header."]
pub type HEAD_EN_R = crate::BitReader;
#[doc = "Field `HEAD_EN` writer - Set this bit to encode the data packet with a formatting header."]
pub type HEAD_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `CRC_REC_EN` reader - Set this bit to enable UHCI to receive the 16 bit CRC."]
pub type CRC_REC_EN_R = crate::BitReader;
#[doc = "Field `CRC_REC_EN` writer - Set this bit to enable UHCI to receive the 16 bit CRC."]
pub type CRC_REC_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `UART_IDLE_EOF_EN` reader - If this bit is set to 1 UHCI will end the payload receiving process when UART has been in idle state."]
pub type UART_IDLE_EOF_EN_R = crate::BitReader;
#[doc = "Field `UART_IDLE_EOF_EN` writer - If this bit is set to 1 UHCI will end the payload receiving process when UART has been in idle state."]
pub type UART_IDLE_EOF_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `LEN_EOF_EN` reader - If this bit is set to 1 UHCI decoder receiving payload data is end when the receiving byte count has reached the specified value. The value is payload length indicated by UHCI packet header when UHCI_HEAD_EN is 1 or the value is configuration value when UHCI_HEAD_EN is 0. If this bit is set to 0 UHCI decoder receiving payload data is end when 0xc0 is received."]
pub type LEN_EOF_EN_R = crate::BitReader;
#[doc = "Field `LEN_EOF_EN` writer - If this bit is set to 1 UHCI decoder receiving payload data is end when the receiving byte count has reached the specified value. The value is payload length indicated by UHCI packet header when UHCI_HEAD_EN is 1 or the value is configuration value when UHCI_HEAD_EN is 0. If this bit is set to 0 UHCI decoder receiving payload data is end when 0xc0 is received."]
pub type LEN_EOF_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ENCODE_CRC_EN` reader - Set this bit to enable data integrity checking by appending a 16 bit CCITT-CRC to end of the payload."]
pub type ENCODE_CRC_EN_R = crate::BitReader;
#[doc = "Field `ENCODE_CRC_EN` writer - Set this bit to enable data integrity checking by appending a 16 bit CCITT-CRC to end of the payload."]
pub type ENCODE_CRC_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `CLK_EN` reader - 1'b1: Force clock on for register. 1'b0: Support clock only when application writes registers."]
pub type CLK_EN_R = crate::BitReader;
#[doc = "Field `CLK_EN` writer - 1'b1: Force clock on for register. 1'b0: Support clock only when application writes registers."]
pub type CLK_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `UART_RX_BRK_EOF_EN` reader - If this bit is set to 1 UHCI will end payload receive process when NULL frame is received by UART."]
pub type UART_RX_BRK_EOF_EN_R = crate::BitReader;
#[doc = "Field `UART_RX_BRK_EOF_EN` writer - If this bit is set to 1 UHCI will end payload receive process when NULL frame is received by UART."]
pub type UART_RX_BRK_EOF_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 0 - Write 1 then write 0 to this bit to reset decode state machine."]
    #[inline(always)]
    pub fn tx_rst(&self) -> TX_RST_R {
        TX_RST_R::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - Write 1 then write 0 to this bit to reset encode state machine."]
    #[inline(always)]
    pub fn rx_rst(&self) -> RX_RST_R {
        RX_RST_R::new(((self.bits >> 1) & 1) != 0)
    }
    #[doc = "Bit 2 - Set this bit to link up HCI and UART0."]
    #[inline(always)]
    pub fn uart0_ce(&self) -> UART0_CE_R {
        UART0_CE_R::new(((self.bits >> 2) & 1) != 0)
    }
    #[doc = "Bit 3 - Set this bit to link up HCI and UART1."]
    #[inline(always)]
    pub fn uart1_ce(&self) -> UART1_CE_R {
        UART1_CE_R::new(((self.bits >> 3) & 1) != 0)
    }
    #[doc = "Bit 5 - Set this bit to separate the data frame using a special char."]
    #[inline(always)]
    pub fn seper_en(&self) -> SEPER_EN_R {
        SEPER_EN_R::new(((self.bits >> 5) & 1) != 0)
    }
    #[doc = "Bit 6 - Set this bit to encode the data packet with a formatting header."]
    #[inline(always)]
    pub fn head_en(&self) -> HEAD_EN_R {
        HEAD_EN_R::new(((self.bits >> 6) & 1) != 0)
    }
    #[doc = "Bit 7 - Set this bit to enable UHCI to receive the 16 bit CRC."]
    #[inline(always)]
    pub fn crc_rec_en(&self) -> CRC_REC_EN_R {
        CRC_REC_EN_R::new(((self.bits >> 7) & 1) != 0)
    }
    #[doc = "Bit 8 - If this bit is set to 1 UHCI will end the payload receiving process when UART has been in idle state."]
    #[inline(always)]
    pub fn uart_idle_eof_en(&self) -> UART_IDLE_EOF_EN_R {
        UART_IDLE_EOF_EN_R::new(((self.bits >> 8) & 1) != 0)
    }
    #[doc = "Bit 9 - If this bit is set to 1 UHCI decoder receiving payload data is end when the receiving byte count has reached the specified value. The value is payload length indicated by UHCI packet header when UHCI_HEAD_EN is 1 or the value is configuration value when UHCI_HEAD_EN is 0. If this bit is set to 0 UHCI decoder receiving payload data is end when 0xc0 is received."]
    #[inline(always)]
    pub fn len_eof_en(&self) -> LEN_EOF_EN_R {
        LEN_EOF_EN_R::new(((self.bits >> 9) & 1) != 0)
    }
    #[doc = "Bit 10 - Set this bit to enable data integrity checking by appending a 16 bit CCITT-CRC to end of the payload."]
    #[inline(always)]
    pub fn encode_crc_en(&self) -> ENCODE_CRC_EN_R {
        ENCODE_CRC_EN_R::new(((self.bits >> 10) & 1) != 0)
    }
    #[doc = "Bit 11 - 1'b1: Force clock on for register. 1'b0: Support clock only when application writes registers."]
    #[inline(always)]
    pub fn clk_en(&self) -> CLK_EN_R {
        CLK_EN_R::new(((self.bits >> 11) & 1) != 0)
    }
    #[doc = "Bit 12 - If this bit is set to 1 UHCI will end payload receive process when NULL frame is received by UART."]
    #[inline(always)]
    pub fn uart_rx_brk_eof_en(&self) -> UART_RX_BRK_EOF_EN_R {
        UART_RX_BRK_EOF_EN_R::new(((self.bits >> 12) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("CONF0")
            .field("tx_rst", &self.tx_rst())
            .field("rx_rst", &self.rx_rst())
            .field("uart0_ce", &self.uart0_ce())
            .field("uart1_ce", &self.uart1_ce())
            .field("seper_en", &self.seper_en())
            .field("head_en", &self.head_en())
            .field("crc_rec_en", &self.crc_rec_en())
            .field("uart_idle_eof_en", &self.uart_idle_eof_en())
            .field("len_eof_en", &self.len_eof_en())
            .field("encode_crc_en", &self.encode_crc_en())
            .field("clk_en", &self.clk_en())
            .field("uart_rx_brk_eof_en", &self.uart_rx_brk_eof_en())
            .finish()
    }
}
impl W {
    #[doc = "Bit 0 - Write 1 then write 0 to this bit to reset decode state machine."]
    #[inline(always)]
    pub fn tx_rst(&mut self) -> TX_RST_W<'_, CONF0_SPEC> {
        TX_RST_W::new(self, 0)
    }
    #[doc = "Bit 1 - Write 1 then write 0 to this bit to reset encode state machine."]
    #[inline(always)]
    pub fn rx_rst(&mut self) -> RX_RST_W<'_, CONF0_SPEC> {
        RX_RST_W::new(self, 1)
    }
    #[doc = "Bit 2 - Set this bit to link up HCI and UART0."]
    #[inline(always)]
    pub fn uart0_ce(&mut self) -> UART0_CE_W<'_, CONF0_SPEC> {
        UART0_CE_W::new(self, 2)
    }
    #[doc = "Bit 3 - Set this bit to link up HCI and UART1."]
    #[inline(always)]
    pub fn uart1_ce(&mut self) -> UART1_CE_W<'_, CONF0_SPEC> {
        UART1_CE_W::new(self, 3)
    }
    #[doc = "Bit 5 - Set this bit to separate the data frame using a special char."]
    #[inline(always)]
    pub fn seper_en(&mut self) -> SEPER_EN_W<'_, CONF0_SPEC> {
        SEPER_EN_W::new(self, 5)
    }
    #[doc = "Bit 6 - Set this bit to encode the data packet with a formatting header."]
    #[inline(always)]
    pub fn head_en(&mut self) -> HEAD_EN_W<'_, CONF0_SPEC> {
        HEAD_EN_W::new(self, 6)
    }
    #[doc = "Bit 7 - Set this bit to enable UHCI to receive the 16 bit CRC."]
    #[inline(always)]
    pub fn crc_rec_en(&mut self) -> CRC_REC_EN_W<'_, CONF0_SPEC> {
        CRC_REC_EN_W::new(self, 7)
    }
    #[doc = "Bit 8 - If this bit is set to 1 UHCI will end the payload receiving process when UART has been in idle state."]
    #[inline(always)]
    pub fn uart_idle_eof_en(&mut self) -> UART_IDLE_EOF_EN_W<'_, CONF0_SPEC> {
        UART_IDLE_EOF_EN_W::new(self, 8)
    }
    #[doc = "Bit 9 - If this bit is set to 1 UHCI decoder receiving payload data is end when the receiving byte count has reached the specified value. The value is payload length indicated by UHCI packet header when UHCI_HEAD_EN is 1 or the value is configuration value when UHCI_HEAD_EN is 0. If this bit is set to 0 UHCI decoder receiving payload data is end when 0xc0 is received."]
    #[inline(always)]
    pub fn len_eof_en(&mut self) -> LEN_EOF_EN_W<'_, CONF0_SPEC> {
        LEN_EOF_EN_W::new(self, 9)
    }
    #[doc = "Bit 10 - Set this bit to enable data integrity checking by appending a 16 bit CCITT-CRC to end of the payload."]
    #[inline(always)]
    pub fn encode_crc_en(&mut self) -> ENCODE_CRC_EN_W<'_, CONF0_SPEC> {
        ENCODE_CRC_EN_W::new(self, 10)
    }
    #[doc = "Bit 11 - 1'b1: Force clock on for register. 1'b0: Support clock only when application writes registers."]
    #[inline(always)]
    pub fn clk_en(&mut self) -> CLK_EN_W<'_, CONF0_SPEC> {
        CLK_EN_W::new(self, 11)
    }
    #[doc = "Bit 12 - If this bit is set to 1 UHCI will end payload receive process when NULL frame is received by UART."]
    #[inline(always)]
    pub fn uart_rx_brk_eof_en(&mut self) -> UART_RX_BRK_EOF_EN_W<'_, CONF0_SPEC> {
        UART_RX_BRK_EOF_EN_W::new(self, 12)
    }
}
#[doc = "UHCI Configuration Register0\n\nYou can [`read`](crate::Reg::read) this register and get [`conf0::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`conf0::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct CONF0_SPEC;
impl crate::RegisterSpec for CONF0_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`conf0::R`](R) reader structure"]
impl crate::Readable for CONF0_SPEC {}
#[doc = "`write(|w| ..)` method takes [`conf0::W`](W) writer structure"]
impl crate::Writable for CONF0_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets CONF0 to value 0x06e0"]
impl crate::Resettable for CONF0_SPEC {
    const RESET_VALUE: u32 = 0x06e0;
}
