#[doc = "Register `TXRX_PATH_DELAY` reader"]
pub type R = crate::R<TXRX_PATH_DELAY_SPEC>;
#[doc = "Register `TXRX_PATH_DELAY` writer"]
pub type W = crate::W<TXRX_PATH_DELAY_SPEC>;
#[doc = "Field `TX_PATH_DELAY` reader - "]
pub type TX_PATH_DELAY_R = crate::FieldReader;
#[doc = "Field `TX_PATH_DELAY` writer - "]
pub type TX_PATH_DELAY_W<'a, REG> = crate::FieldWriter<'a, REG, 6>;
#[doc = "Field `RX_PATH_DELAY` reader - "]
pub type RX_PATH_DELAY_R = crate::FieldReader;
#[doc = "Field `RX_PATH_DELAY` writer - "]
pub type RX_PATH_DELAY_W<'a, REG> = crate::FieldWriter<'a, REG, 6>;
impl R {
    #[doc = "Bits 0:5"]
    #[inline(always)]
    pub fn tx_path_delay(&self) -> TX_PATH_DELAY_R {
        TX_PATH_DELAY_R::new((self.bits & 0x3f) as u8)
    }
    #[doc = "Bits 16:21"]
    #[inline(always)]
    pub fn rx_path_delay(&self) -> RX_PATH_DELAY_R {
        RX_PATH_DELAY_R::new(((self.bits >> 16) & 0x3f) as u8)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("TXRX_PATH_DELAY")
            .field("tx_path_delay", &self.tx_path_delay())
            .field("rx_path_delay", &self.rx_path_delay())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:5"]
    #[inline(always)]
    pub fn tx_path_delay(&mut self) -> TX_PATH_DELAY_W<'_, TXRX_PATH_DELAY_SPEC> {
        TX_PATH_DELAY_W::new(self, 0)
    }
    #[doc = "Bits 16:21"]
    #[inline(always)]
    pub fn rx_path_delay(&mut self) -> RX_PATH_DELAY_W<'_, TXRX_PATH_DELAY_SPEC> {
        RX_PATH_DELAY_W::new(self, 16)
    }
}
#[doc = "\n\nYou can [`read`](crate::Reg::read) this register and get [`txrx_path_delay::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`txrx_path_delay::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct TXRX_PATH_DELAY_SPEC;
impl crate::RegisterSpec for TXRX_PATH_DELAY_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`txrx_path_delay::R`](R) reader structure"]
impl crate::Readable for TXRX_PATH_DELAY_SPEC {}
#[doc = "`write(|w| ..)` method takes [`txrx_path_delay::W`](W) writer structure"]
impl crate::Writable for TXRX_PATH_DELAY_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets TXRX_PATH_DELAY to value 0"]
impl crate::Resettable for TXRX_PATH_DELAY_SPEC {}
