#[doc = "Register `TXBRK_CONF` reader"]
pub type R = crate::R<TXBRK_CONF_SPEC>;
#[doc = "Register `TXBRK_CONF` writer"]
pub type W = crate::W<TXBRK_CONF_SPEC>;
#[doc = "Field `TX_BRK_NUM` reader - This register is used to configure the number of 0 to be sent after the process of sending data is done. It is active when txd_brk is set to 1."]
pub type TX_BRK_NUM_R = crate::FieldReader;
#[doc = "Field `TX_BRK_NUM` writer - This register is used to configure the number of 0 to be sent after the process of sending data is done. It is active when txd_brk is set to 1."]
pub type TX_BRK_NUM_W<'a, REG> = crate::FieldWriter<'a, REG, 8>;
impl R {
    #[doc = "Bits 0:7 - This register is used to configure the number of 0 to be sent after the process of sending data is done. It is active when txd_brk is set to 1."]
    #[inline(always)]
    pub fn tx_brk_num(&self) -> TX_BRK_NUM_R {
        TX_BRK_NUM_R::new((self.bits & 0xff) as u8)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("TXBRK_CONF")
            .field("tx_brk_num", &self.tx_brk_num())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:7 - This register is used to configure the number of 0 to be sent after the process of sending data is done. It is active when txd_brk is set to 1."]
    #[inline(always)]
    pub fn tx_brk_num(&mut self) -> TX_BRK_NUM_W<'_, TXBRK_CONF_SPEC> {
        TX_BRK_NUM_W::new(self, 0)
    }
}
#[doc = "Tx Break character configuration\n\nYou can [`read`](crate::Reg::read) this register and get [`txbrk_conf::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`txbrk_conf::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct TXBRK_CONF_SPEC;
impl crate::RegisterSpec for TXBRK_CONF_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`txbrk_conf::R`](R) reader structure"]
impl crate::Readable for TXBRK_CONF_SPEC {}
#[doc = "`write(|w| ..)` method takes [`txbrk_conf::W`](W) writer structure"]
impl crate::Writable for TXBRK_CONF_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets TXBRK_CONF to value 0x0a"]
impl crate::Resettable for TXBRK_CONF_SPEC {
    const RESET_VALUE: u32 = 0x0a;
}
