#[doc = "Register `INT_CLR` writer"]
pub type W = crate::W<INT_CLR_SPEC>;
#[doc = "Field `RX_START` writer - a"]
pub type RX_START_W<'a, REG> = crate::BitWriter1C<'a, REG>;
#[doc = "Field `TX_START` writer - a"]
pub type TX_START_W<'a, REG> = crate::BitWriter1C<'a, REG>;
#[doc = "Field `RX_HUNG` writer - a"]
pub type RX_HUNG_W<'a, REG> = crate::BitWriter1C<'a, REG>;
#[doc = "Field `TX_HUNG` writer - a"]
pub type TX_HUNG_W<'a, REG> = crate::BitWriter1C<'a, REG>;
#[doc = "Field `SEND_S_REG_Q` writer - a"]
pub type SEND_S_REG_Q_W<'a, REG> = crate::BitWriter1C<'a, REG>;
#[doc = "Field `SEND_A_REG_Q` writer - a"]
pub type SEND_A_REG_Q_W<'a, REG> = crate::BitWriter1C<'a, REG>;
#[doc = "Field `OUTLINK_EOF_ERR` writer - a"]
pub type OUTLINK_EOF_ERR_W<'a, REG> = crate::BitWriter1C<'a, REG>;
#[doc = "Field `APP_CTRL0` writer - a"]
pub type APP_CTRL0_W<'a, REG> = crate::BitWriter1C<'a, REG>;
#[doc = "Field `APP_CTRL1` writer - a"]
pub type APP_CTRL1_W<'a, REG> = crate::BitWriter1C<'a, REG>;
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for crate::generic::Reg<INT_CLR_SPEC> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "(not readable)")
    }
}
impl W {
    #[doc = "Bit 0 - a"]
    #[inline(always)]
    pub fn rx_start(&mut self) -> RX_START_W<'_, INT_CLR_SPEC> {
        RX_START_W::new(self, 0)
    }
    #[doc = "Bit 1 - a"]
    #[inline(always)]
    pub fn tx_start(&mut self) -> TX_START_W<'_, INT_CLR_SPEC> {
        TX_START_W::new(self, 1)
    }
    #[doc = "Bit 2 - a"]
    #[inline(always)]
    pub fn rx_hung(&mut self) -> RX_HUNG_W<'_, INT_CLR_SPEC> {
        RX_HUNG_W::new(self, 2)
    }
    #[doc = "Bit 3 - a"]
    #[inline(always)]
    pub fn tx_hung(&mut self) -> TX_HUNG_W<'_, INT_CLR_SPEC> {
        TX_HUNG_W::new(self, 3)
    }
    #[doc = "Bit 4 - a"]
    #[inline(always)]
    pub fn send_s_reg_q(&mut self) -> SEND_S_REG_Q_W<'_, INT_CLR_SPEC> {
        SEND_S_REG_Q_W::new(self, 4)
    }
    #[doc = "Bit 5 - a"]
    #[inline(always)]
    pub fn send_a_reg_q(&mut self) -> SEND_A_REG_Q_W<'_, INT_CLR_SPEC> {
        SEND_A_REG_Q_W::new(self, 5)
    }
    #[doc = "Bit 6 - a"]
    #[inline(always)]
    pub fn outlink_eof_err(&mut self) -> OUTLINK_EOF_ERR_W<'_, INT_CLR_SPEC> {
        OUTLINK_EOF_ERR_W::new(self, 6)
    }
    #[doc = "Bit 7 - a"]
    #[inline(always)]
    pub fn app_ctrl0(&mut self) -> APP_CTRL0_W<'_, INT_CLR_SPEC> {
        APP_CTRL0_W::new(self, 7)
    }
    #[doc = "Bit 8 - a"]
    #[inline(always)]
    pub fn app_ctrl1(&mut self) -> APP_CTRL1_W<'_, INT_CLR_SPEC> {
        APP_CTRL1_W::new(self, 8)
    }
}
#[doc = "a\n\nYou can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`int_clr::W`](W). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct INT_CLR_SPEC;
impl crate::RegisterSpec for INT_CLR_SPEC {
    type Ux = u32;
}
#[doc = "`write(|w| ..)` method takes [`int_clr::W`](W) writer structure"]
impl crate::Writable for INT_CLR_SPEC {
    type Safety = crate::Unsafe;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0x01ff;
}
#[doc = "`reset()` method sets INT_CLR to value 0"]
impl crate::Resettable for INT_CLR_SPEC {}
