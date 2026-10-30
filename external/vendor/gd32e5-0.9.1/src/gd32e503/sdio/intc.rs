#[doc = "Register `INTC` writer"]
pub type W = crate::W<IntcSpec>;
#[doc = "Field `CCRCERRC` writer - CCRCERR flag clear bit"]
pub type CcrcerrcW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `DTCRCERRC` writer - DTCRCERR flag clear bit"]
pub type DtcrcerrcW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `CMDTMOUTC` writer - CMDTMOUT flag clear bit"]
pub type CmdtmoutcW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `DTTMOUTC` writer - DTTMOUT flag clear bit"]
pub type DttmoutcW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `TXUREC` writer - TXURE flag clear bit"]
pub type TxurecW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `RXOREC` writer - RXORE flag clear bit"]
pub type RxorecW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `CMDRECVC` writer - CMDRECV flag clear bit"]
pub type CmdrecvcW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `CMDSENDC` writer - CMDSEND flag clear bit"]
pub type CmdsendcW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `DTENDC` writer - DTEND flag clear bit"]
pub type DtendcW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `STBITEC` writer - STBITE flag clear bit"]
pub type StbitecW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `DTBLKENDC` writer - DTBLKEND flag clear bit"]
pub type DtblkendcW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SDIOINTC` writer - SDIOINT flag clear bit"]
pub type SdiointcW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ATAENDC` writer - ATAEND flag clear bit"]
pub type AtaendcW<'a, REG> = crate::BitWriter<'a, REG>;
impl W {
    #[doc = "Bit 0 - CCRCERR flag clear bit"]
    #[inline(always)]
    #[must_use]
    pub fn ccrcerrc(&mut self) -> CcrcerrcW<IntcSpec> {
        CcrcerrcW::new(self, 0)
    }
    #[doc = "Bit 1 - DTCRCERR flag clear bit"]
    #[inline(always)]
    #[must_use]
    pub fn dtcrcerrc(&mut self) -> DtcrcerrcW<IntcSpec> {
        DtcrcerrcW::new(self, 1)
    }
    #[doc = "Bit 2 - CMDTMOUT flag clear bit"]
    #[inline(always)]
    #[must_use]
    pub fn cmdtmoutc(&mut self) -> CmdtmoutcW<IntcSpec> {
        CmdtmoutcW::new(self, 2)
    }
    #[doc = "Bit 3 - DTTMOUT flag clear bit"]
    #[inline(always)]
    #[must_use]
    pub fn dttmoutc(&mut self) -> DttmoutcW<IntcSpec> {
        DttmoutcW::new(self, 3)
    }
    #[doc = "Bit 4 - TXURE flag clear bit"]
    #[inline(always)]
    #[must_use]
    pub fn txurec(&mut self) -> TxurecW<IntcSpec> {
        TxurecW::new(self, 4)
    }
    #[doc = "Bit 5 - RXORE flag clear bit"]
    #[inline(always)]
    #[must_use]
    pub fn rxorec(&mut self) -> RxorecW<IntcSpec> {
        RxorecW::new(self, 5)
    }
    #[doc = "Bit 6 - CMDRECV flag clear bit"]
    #[inline(always)]
    #[must_use]
    pub fn cmdrecvc(&mut self) -> CmdrecvcW<IntcSpec> {
        CmdrecvcW::new(self, 6)
    }
    #[doc = "Bit 7 - CMDSEND flag clear bit"]
    #[inline(always)]
    #[must_use]
    pub fn cmdsendc(&mut self) -> CmdsendcW<IntcSpec> {
        CmdsendcW::new(self, 7)
    }
    #[doc = "Bit 8 - DTEND flag clear bit"]
    #[inline(always)]
    #[must_use]
    pub fn dtendc(&mut self) -> DtendcW<IntcSpec> {
        DtendcW::new(self, 8)
    }
    #[doc = "Bit 9 - STBITE flag clear bit"]
    #[inline(always)]
    #[must_use]
    pub fn stbitec(&mut self) -> StbitecW<IntcSpec> {
        StbitecW::new(self, 9)
    }
    #[doc = "Bit 10 - DTBLKEND flag clear bit"]
    #[inline(always)]
    #[must_use]
    pub fn dtblkendc(&mut self) -> DtblkendcW<IntcSpec> {
        DtblkendcW::new(self, 10)
    }
    #[doc = "Bit 22 - SDIOINT flag clear bit"]
    #[inline(always)]
    #[must_use]
    pub fn sdiointc(&mut self) -> SdiointcW<IntcSpec> {
        SdiointcW::new(self, 22)
    }
    #[doc = "Bit 23 - ATAEND flag clear bit"]
    #[inline(always)]
    #[must_use]
    pub fn ataendc(&mut self) -> AtaendcW<IntcSpec> {
        AtaendcW::new(self, 23)
    }
}
#[doc = "Interrupt clear register\n\nYou can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`intc::W`](W). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct IntcSpec;
impl crate::RegisterSpec for IntcSpec {
    type Ux = u32;
}
#[doc = "`write(|w| ..)` method takes [`intc::W`](W) writer structure"]
impl crate::Writable for IntcSpec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets INTC to value 0"]
impl crate::Resettable for IntcSpec {
    const RESET_VALUE: u32 = 0;
}
