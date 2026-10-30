#[doc = "Register `CMD` writer"]
pub type W = crate::W<CmdSpec>;
#[doc = "Field `ABDCMD` writer - Auto baudrate detection command"]
pub type AbdcmdW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SBKCMD` writer - Send break command"]
pub type SbkcmdW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `MMCMD` writer - Mute mode command"]
pub type MmcmdW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `RXFCMD` writer - Receive data flush command"]
pub type RxfcmdW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `TXFCMD` writer - Transmit data flush request"]
pub type TxfcmdW<'a, REG> = crate::BitWriter<'a, REG>;
impl W {
    #[doc = "Bit 0 - Auto baudrate detection command"]
    #[inline(always)]
    #[must_use]
    pub fn abdcmd(&mut self) -> AbdcmdW<CmdSpec> {
        AbdcmdW::new(self, 0)
    }
    #[doc = "Bit 1 - Send break command"]
    #[inline(always)]
    #[must_use]
    pub fn sbkcmd(&mut self) -> SbkcmdW<CmdSpec> {
        SbkcmdW::new(self, 1)
    }
    #[doc = "Bit 2 - Mute mode command"]
    #[inline(always)]
    #[must_use]
    pub fn mmcmd(&mut self) -> MmcmdW<CmdSpec> {
        MmcmdW::new(self, 2)
    }
    #[doc = "Bit 3 - Receive data flush command"]
    #[inline(always)]
    #[must_use]
    pub fn rxfcmd(&mut self) -> RxfcmdW<CmdSpec> {
        RxfcmdW::new(self, 3)
    }
    #[doc = "Bit 4 - Transmit data flush request"]
    #[inline(always)]
    #[must_use]
    pub fn txfcmd(&mut self) -> TxfcmdW<CmdSpec> {
        TxfcmdW::new(self, 4)
    }
}
#[doc = "Command register (USART_CMD)\n\nYou can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`cmd::W`](W). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct CmdSpec;
impl crate::RegisterSpec for CmdSpec {
    type Ux = u32;
}
#[doc = "`write(|w| ..)` method takes [`cmd::W`](W) writer structure"]
impl crate::Writable for CmdSpec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets CMD to value 0"]
impl crate::Resettable for CmdSpec {
    const RESET_VALUE: u32 = 0;
}
