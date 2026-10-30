#[doc = "Register `ST1DTCTL` reader"]
pub type R = crate::R<St1dtctlSpec>;
#[doc = "Register `ST1DTCTL` writer"]
pub type W = crate::W<St1dtctlSpec>;
#[doc = "Field `DTRCFG` reader - Falling edge dead-time value"]
pub type DtrcfgR = crate::FieldReader<u16>;
#[doc = "Field `DTRCFG` writer - Falling edge dead-time value"]
pub type DtrcfgW<'a, REG> = crate::FieldWriter<'a, REG, 9, u16>;
#[doc = "Field `DTRS` reader - The sign of falling edge dead-time value"]
pub type DtrsR = crate::BitReader;
#[doc = "Field `DTRS` writer - The sign of falling edge dead-time value"]
pub type DtrsW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `DTGCKDIV` reader - Dead time generator clock division"]
pub type DtgckdivR = crate::FieldReader;
#[doc = "Field `DTGCKDIV` writer - Dead time generator clock division"]
pub type DtgckdivW<'a, REG> = crate::FieldWriter<'a, REG, 4>;
#[doc = "Field `DTRSPROT` reader - Dead-time rising edge protection for sign"]
pub type DtrsprotR = crate::BitReader;
#[doc = "Field `DTRSPROT` writer - Dead-time rising edge protection for sign"]
pub type DtrsprotW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `DTRSVPROT` reader - Dead-time rising edge protection for value and sign"]
pub type DtrsvprotR = crate::BitReader;
#[doc = "Field `DTRSVPROT` writer - Dead-time rising edge protection for value and sign"]
pub type DtrsvprotW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `DTFCFG` reader - Falling edge dead-time value"]
pub type DtfcfgR = crate::FieldReader<u16>;
#[doc = "Field `DTFCFG` writer - Falling edge dead-time value"]
pub type DtfcfgW<'a, REG> = crate::FieldWriter<'a, REG, 9, u16>;
#[doc = "Field `DTFS` reader - The sign of falling edge dead-time value"]
pub type DtfsR = crate::BitReader;
#[doc = "Field `DTFS` writer - The sign of falling edge dead-time value"]
pub type DtfsW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `DTFSPROT` reader - Dead-time falling edge protection for sign"]
pub type DtfsprotR = crate::BitReader;
#[doc = "Field `DTFSPROT` writer - Dead-time falling edge protection for sign"]
pub type DtfsprotW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `DTFSVPROT` reader - Dead-time falling edge protection for value and sign"]
pub type DtfsvprotR = crate::BitReader;
#[doc = "Field `DTFSVPROT` writer - Dead-time falling edge protection for value and sign"]
pub type DtfsvprotW<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bits 0:8 - Falling edge dead-time value"]
    #[inline(always)]
    pub fn dtrcfg(&self) -> DtrcfgR {
        DtrcfgR::new((self.bits & 0x01ff) as u16)
    }
    #[doc = "Bit 9 - The sign of falling edge dead-time value"]
    #[inline(always)]
    pub fn dtrs(&self) -> DtrsR {
        DtrsR::new(((self.bits >> 9) & 1) != 0)
    }
    #[doc = "Bits 10:13 - Dead time generator clock division"]
    #[inline(always)]
    pub fn dtgckdiv(&self) -> DtgckdivR {
        DtgckdivR::new(((self.bits >> 10) & 0x0f) as u8)
    }
    #[doc = "Bit 14 - Dead-time rising edge protection for sign"]
    #[inline(always)]
    pub fn dtrsprot(&self) -> DtrsprotR {
        DtrsprotR::new(((self.bits >> 14) & 1) != 0)
    }
    #[doc = "Bit 15 - Dead-time rising edge protection for value and sign"]
    #[inline(always)]
    pub fn dtrsvprot(&self) -> DtrsvprotR {
        DtrsvprotR::new(((self.bits >> 15) & 1) != 0)
    }
    #[doc = "Bits 16:24 - Falling edge dead-time value"]
    #[inline(always)]
    pub fn dtfcfg(&self) -> DtfcfgR {
        DtfcfgR::new(((self.bits >> 16) & 0x01ff) as u16)
    }
    #[doc = "Bit 25 - The sign of falling edge dead-time value"]
    #[inline(always)]
    pub fn dtfs(&self) -> DtfsR {
        DtfsR::new(((self.bits >> 25) & 1) != 0)
    }
    #[doc = "Bit 30 - Dead-time falling edge protection for sign"]
    #[inline(always)]
    pub fn dtfsprot(&self) -> DtfsprotR {
        DtfsprotR::new(((self.bits >> 30) & 1) != 0)
    }
    #[doc = "Bit 31 - Dead-time falling edge protection for value and sign"]
    #[inline(always)]
    pub fn dtfsvprot(&self) -> DtfsvprotR {
        DtfsvprotR::new(((self.bits >> 31) & 1) != 0)
    }
}
impl W {
    #[doc = "Bits 0:8 - Falling edge dead-time value"]
    #[inline(always)]
    #[must_use]
    pub fn dtrcfg(&mut self) -> DtrcfgW<St1dtctlSpec> {
        DtrcfgW::new(self, 0)
    }
    #[doc = "Bit 9 - The sign of falling edge dead-time value"]
    #[inline(always)]
    #[must_use]
    pub fn dtrs(&mut self) -> DtrsW<St1dtctlSpec> {
        DtrsW::new(self, 9)
    }
    #[doc = "Bits 10:13 - Dead time generator clock division"]
    #[inline(always)]
    #[must_use]
    pub fn dtgckdiv(&mut self) -> DtgckdivW<St1dtctlSpec> {
        DtgckdivW::new(self, 10)
    }
    #[doc = "Bit 14 - Dead-time rising edge protection for sign"]
    #[inline(always)]
    #[must_use]
    pub fn dtrsprot(&mut self) -> DtrsprotW<St1dtctlSpec> {
        DtrsprotW::new(self, 14)
    }
    #[doc = "Bit 15 - Dead-time rising edge protection for value and sign"]
    #[inline(always)]
    #[must_use]
    pub fn dtrsvprot(&mut self) -> DtrsvprotW<St1dtctlSpec> {
        DtrsvprotW::new(self, 15)
    }
    #[doc = "Bits 16:24 - Falling edge dead-time value"]
    #[inline(always)]
    #[must_use]
    pub fn dtfcfg(&mut self) -> DtfcfgW<St1dtctlSpec> {
        DtfcfgW::new(self, 16)
    }
    #[doc = "Bit 25 - The sign of falling edge dead-time value"]
    #[inline(always)]
    #[must_use]
    pub fn dtfs(&mut self) -> DtfsW<St1dtctlSpec> {
        DtfsW::new(self, 25)
    }
    #[doc = "Bit 30 - Dead-time falling edge protection for sign"]
    #[inline(always)]
    #[must_use]
    pub fn dtfsprot(&mut self) -> DtfsprotW<St1dtctlSpec> {
        DtfsprotW::new(self, 30)
    }
    #[doc = "Bit 31 - Dead-time falling edge protection for value and sign"]
    #[inline(always)]
    #[must_use]
    pub fn dtfsvprot(&mut self) -> DtfsvprotW<St1dtctlSpec> {
        DtfsvprotW::new(self, 31)
    }
}
#[doc = "SHRTIMER Slave_TIMER1 dead-time control register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`st1dtctl::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`st1dtctl::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct St1dtctlSpec;
impl crate::RegisterSpec for St1dtctlSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`st1dtctl::R`](R) reader structure"]
impl crate::Readable for St1dtctlSpec {}
#[doc = "`write(|w| ..)` method takes [`st1dtctl::W`](W) writer structure"]
impl crate::Writable for St1dtctlSpec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets ST1DTCTL to value 0"]
impl crate::Resettable for St1dtctlSpec {
    const RESET_VALUE: u32 = 0;
}
