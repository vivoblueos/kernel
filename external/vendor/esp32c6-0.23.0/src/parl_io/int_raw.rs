#[doc = "Register `INT_RAW` reader"]
pub type R = crate::R<INT_RAW_SPEC>;
#[doc = "Register `INT_RAW` writer"]
pub type W = crate::W<INT_RAW_SPEC>;
#[doc = "Field `TX_FIFO_REMPTY` reader - The raw interrupt status of TX_FIFO_REMPTY_INTR."]
pub type TX_FIFO_REMPTY_R = crate::BitReader;
#[doc = "Field `TX_FIFO_REMPTY` writer - The raw interrupt status of TX_FIFO_REMPTY_INTR."]
pub type TX_FIFO_REMPTY_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `RX_FIFO_WOVF` reader - The raw interrupt status of RX_FIFO_WOVF_INTR."]
pub type RX_FIFO_WOVF_R = crate::BitReader;
#[doc = "Field `RX_FIFO_WOVF` writer - The raw interrupt status of RX_FIFO_WOVF_INTR."]
pub type RX_FIFO_WOVF_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `TX_EOF` reader - The raw interrupt status of TX_EOF_INTR."]
pub type TX_EOF_R = crate::BitReader;
#[doc = "Field `TX_EOF` writer - The raw interrupt status of TX_EOF_INTR."]
pub type TX_EOF_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 0 - The raw interrupt status of TX_FIFO_REMPTY_INTR."]
    #[inline(always)]
    pub fn tx_fifo_rempty(&self) -> TX_FIFO_REMPTY_R {
        TX_FIFO_REMPTY_R::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - The raw interrupt status of RX_FIFO_WOVF_INTR."]
    #[inline(always)]
    pub fn rx_fifo_wovf(&self) -> RX_FIFO_WOVF_R {
        RX_FIFO_WOVF_R::new(((self.bits >> 1) & 1) != 0)
    }
    #[doc = "Bit 2 - The raw interrupt status of TX_EOF_INTR."]
    #[inline(always)]
    pub fn tx_eof(&self) -> TX_EOF_R {
        TX_EOF_R::new(((self.bits >> 2) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("INT_RAW")
            .field("tx_fifo_rempty", &self.tx_fifo_rempty())
            .field("rx_fifo_wovf", &self.rx_fifo_wovf())
            .field("tx_eof", &self.tx_eof())
            .finish()
    }
}
impl W {
    #[doc = "Bit 0 - The raw interrupt status of TX_FIFO_REMPTY_INTR."]
    #[inline(always)]
    pub fn tx_fifo_rempty(&mut self) -> TX_FIFO_REMPTY_W<'_, INT_RAW_SPEC> {
        TX_FIFO_REMPTY_W::new(self, 0)
    }
    #[doc = "Bit 1 - The raw interrupt status of RX_FIFO_WOVF_INTR."]
    #[inline(always)]
    pub fn rx_fifo_wovf(&mut self) -> RX_FIFO_WOVF_W<'_, INT_RAW_SPEC> {
        RX_FIFO_WOVF_W::new(self, 1)
    }
    #[doc = "Bit 2 - The raw interrupt status of TX_EOF_INTR."]
    #[inline(always)]
    pub fn tx_eof(&mut self) -> TX_EOF_W<'_, INT_RAW_SPEC> {
        TX_EOF_W::new(self, 2)
    }
}
#[doc = "Parallel IO interrupt raw singal status register.\n\nYou can [`read`](crate::Reg::read) this register and get [`int_raw::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`int_raw::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct INT_RAW_SPEC;
impl crate::RegisterSpec for INT_RAW_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`int_raw::R`](R) reader structure"]
impl crate::Readable for INT_RAW_SPEC {}
#[doc = "`write(|w| ..)` method takes [`int_raw::W`](W) writer structure"]
impl crate::Writable for INT_RAW_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets INT_RAW to value 0"]
impl crate::Resettable for INT_RAW_SPEC {}
