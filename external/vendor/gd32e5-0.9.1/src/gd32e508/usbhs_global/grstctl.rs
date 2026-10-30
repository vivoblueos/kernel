#[doc = "Register `GRSTCTL` reader"]
pub type R = crate::R<GrstctlSpec>;
#[doc = "Register `GRSTCTL` writer"]
pub type W = crate::W<GrstctlSpec>;
#[doc = "Field `CSRST` reader - Core soft reset"]
pub type CsrstR = crate::BitReader;
#[doc = "Field `CSRST` writer - Core soft reset"]
pub type CsrstW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `HCSRST` reader - HCLK soft reset"]
pub type HcsrstR = crate::BitReader;
#[doc = "Field `HCSRST` writer - HCLK soft reset"]
pub type HcsrstW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `HFCRST` reader - Host frame counter reset"]
pub type HfcrstR = crate::BitReader;
#[doc = "Field `HFCRST` writer - Host frame counter reset"]
pub type HfcrstW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `RXFF` reader - RxFIFO flush"]
pub type RxffR = crate::BitReader;
#[doc = "Field `RXFF` writer - RxFIFO flush"]
pub type RxffW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `TXFF` reader - TxFIFO flush"]
pub type TxffR = crate::BitReader;
#[doc = "Field `TXFF` writer - TxFIFO flush"]
pub type TxffW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `TXFNUM` reader - TxFIFO number"]
pub type TxfnumR = crate::FieldReader;
#[doc = "Field `TXFNUM` writer - TxFIFO number"]
pub type TxfnumW<'a, REG> = crate::FieldWriter<'a, REG, 5>;
#[doc = "Field `DMABSY` reader - DMA Busy"]
pub type DmabsyR = crate::BitReader;
#[doc = "Field `DMAIDL` reader - DMA Idle state"]
pub type DmaidlR = crate::BitReader;
impl R {
    #[doc = "Bit 0 - Core soft reset"]
    #[inline(always)]
    pub fn csrst(&self) -> CsrstR {
        CsrstR::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - HCLK soft reset"]
    #[inline(always)]
    pub fn hcsrst(&self) -> HcsrstR {
        HcsrstR::new(((self.bits >> 1) & 1) != 0)
    }
    #[doc = "Bit 2 - Host frame counter reset"]
    #[inline(always)]
    pub fn hfcrst(&self) -> HfcrstR {
        HfcrstR::new(((self.bits >> 2) & 1) != 0)
    }
    #[doc = "Bit 4 - RxFIFO flush"]
    #[inline(always)]
    pub fn rxff(&self) -> RxffR {
        RxffR::new(((self.bits >> 4) & 1) != 0)
    }
    #[doc = "Bit 5 - TxFIFO flush"]
    #[inline(always)]
    pub fn txff(&self) -> TxffR {
        TxffR::new(((self.bits >> 5) & 1) != 0)
    }
    #[doc = "Bits 6:10 - TxFIFO number"]
    #[inline(always)]
    pub fn txfnum(&self) -> TxfnumR {
        TxfnumR::new(((self.bits >> 6) & 0x1f) as u8)
    }
    #[doc = "Bit 30 - DMA Busy"]
    #[inline(always)]
    pub fn dmabsy(&self) -> DmabsyR {
        DmabsyR::new(((self.bits >> 30) & 1) != 0)
    }
    #[doc = "Bit 31 - DMA Idle state"]
    #[inline(always)]
    pub fn dmaidl(&self) -> DmaidlR {
        DmaidlR::new(((self.bits >> 31) & 1) != 0)
    }
}
impl W {
    #[doc = "Bit 0 - Core soft reset"]
    #[inline(always)]
    #[must_use]
    pub fn csrst(&mut self) -> CsrstW<GrstctlSpec> {
        CsrstW::new(self, 0)
    }
    #[doc = "Bit 1 - HCLK soft reset"]
    #[inline(always)]
    #[must_use]
    pub fn hcsrst(&mut self) -> HcsrstW<GrstctlSpec> {
        HcsrstW::new(self, 1)
    }
    #[doc = "Bit 2 - Host frame counter reset"]
    #[inline(always)]
    #[must_use]
    pub fn hfcrst(&mut self) -> HfcrstW<GrstctlSpec> {
        HfcrstW::new(self, 2)
    }
    #[doc = "Bit 4 - RxFIFO flush"]
    #[inline(always)]
    #[must_use]
    pub fn rxff(&mut self) -> RxffW<GrstctlSpec> {
        RxffW::new(self, 4)
    }
    #[doc = "Bit 5 - TxFIFO flush"]
    #[inline(always)]
    #[must_use]
    pub fn txff(&mut self) -> TxffW<GrstctlSpec> {
        TxffW::new(self, 5)
    }
    #[doc = "Bits 6:10 - TxFIFO number"]
    #[inline(always)]
    #[must_use]
    pub fn txfnum(&mut self) -> TxfnumW<GrstctlSpec> {
        TxfnumW::new(self, 6)
    }
}
#[doc = "Global reset control register (USBHS_GRSTCTL)\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`grstctl::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`grstctl::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct GrstctlSpec;
impl crate::RegisterSpec for GrstctlSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`grstctl::R`](R) reader structure"]
impl crate::Readable for GrstctlSpec {}
#[doc = "`write(|w| ..)` method takes [`grstctl::W`](W) writer structure"]
impl crate::Writable for GrstctlSpec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets GRSTCTL to value 0x8000_0000"]
impl crate::Resettable for GrstctlSpec {
    const RESET_VALUE: u32 = 0x8000_0000;
}
