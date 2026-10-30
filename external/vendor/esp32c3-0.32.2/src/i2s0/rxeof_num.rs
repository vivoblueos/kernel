#[doc = "Register `RXEOF_NUM` reader"]
pub type R = crate::R<RXEOF_NUM_SPEC>;
#[doc = "Register `RXEOF_NUM` writer"]
pub type W = crate::W<RXEOF_NUM_SPEC>;
#[doc = "Field `RX_EOF_NUM` reader - The receive data bit length is (I2S_RX_BITS_MOD\\[4:0\\] + 1) * (REG_RX_EOF_NUM\\[11:0\\] + 1) . It will trigger in_suc_eof interrupt in the configured DMA RX channel."]
pub type RX_EOF_NUM_R = crate::FieldReader<u16>;
#[doc = "Field `RX_EOF_NUM` writer - The receive data bit length is (I2S_RX_BITS_MOD\\[4:0\\] + 1) * (REG_RX_EOF_NUM\\[11:0\\] + 1) . It will trigger in_suc_eof interrupt in the configured DMA RX channel."]
pub type RX_EOF_NUM_W<'a, REG> = crate::FieldWriter<'a, REG, 12, u16>;
impl R {
    #[doc = "Bits 0:11 - The receive data bit length is (I2S_RX_BITS_MOD\\[4:0\\] + 1) * (REG_RX_EOF_NUM\\[11:0\\] + 1) . It will trigger in_suc_eof interrupt in the configured DMA RX channel."]
    #[inline(always)]
    pub fn rx_eof_num(&self) -> RX_EOF_NUM_R {
        RX_EOF_NUM_R::new((self.bits & 0x0fff) as u16)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("RXEOF_NUM")
            .field("rx_eof_num", &self.rx_eof_num())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:11 - The receive data bit length is (I2S_RX_BITS_MOD\\[4:0\\] + 1) * (REG_RX_EOF_NUM\\[11:0\\] + 1) . It will trigger in_suc_eof interrupt in the configured DMA RX channel."]
    #[inline(always)]
    pub fn rx_eof_num(&mut self) -> RX_EOF_NUM_W<'_, RXEOF_NUM_SPEC> {
        RX_EOF_NUM_W::new(self, 0)
    }
}
#[doc = "I2S RX data number control register.\n\nYou can [`read`](crate::Reg::read) this register and get [`rxeof_num::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`rxeof_num::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct RXEOF_NUM_SPEC;
impl crate::RegisterSpec for RXEOF_NUM_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`rxeof_num::R`](R) reader structure"]
impl crate::Readable for RXEOF_NUM_SPEC {}
#[doc = "`write(|w| ..)` method takes [`rxeof_num::W`](W) writer structure"]
impl crate::Writable for RXEOF_NUM_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets RXEOF_NUM to value 0x40"]
impl crate::Resettable for RXEOF_NUM_SPEC {
    const RESET_VALUE: u32 = 0x40;
}
