#[doc = "Register `ST1ACTL` reader"]
pub type R = crate::R<St1actlSpec>;
#[doc = "Register `ST1ACTL` writer"]
pub type W = crate::W<St1actlSpec>;
#[doc = "Field `CNTCKDIV_3` reader - Counter clock division"]
pub type Cntckdiv3R = crate::BitReader;
#[doc = "Field `CNTCKDIV_3` writer - Counter clock division"]
pub type Cntckdiv3W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `DTRCFG_15_9` reader - Rising edge dead-time value configure"]
pub type Dtrcfg15_9R = crate::FieldReader;
#[doc = "Field `DTRCFG_15_9` writer - Rising edge dead-time value configure"]
pub type Dtrcfg15_9W<'a, REG> = crate::FieldWriter<'a, REG, 7>;
#[doc = "Field `DTFCFG_15_9` reader - Falling edge dead-time value configure"]
pub type Dtfcfg15_9R = crate::FieldReader;
#[doc = "Field `DTFCFG_15_9` writer - Falling edge dead-time value configure"]
pub type Dtfcfg15_9W<'a, REG> = crate::FieldWriter<'a, REG, 7>;
impl R {
    #[doc = "Bit 3 - Counter clock division"]
    #[inline(always)]
    pub fn cntckdiv_3(&self) -> Cntckdiv3R {
        Cntckdiv3R::new(((self.bits >> 3) & 1) != 0)
    }
    #[doc = "Bits 9:15 - Rising edge dead-time value configure"]
    #[inline(always)]
    pub fn dtrcfg_15_9(&self) -> Dtrcfg15_9R {
        Dtrcfg15_9R::new(((self.bits >> 9) & 0x7f) as u8)
    }
    #[doc = "Bits 25:31 - Falling edge dead-time value configure"]
    #[inline(always)]
    pub fn dtfcfg_15_9(&self) -> Dtfcfg15_9R {
        Dtfcfg15_9R::new(((self.bits >> 25) & 0x7f) as u8)
    }
}
impl W {
    #[doc = "Bit 3 - Counter clock division"]
    #[inline(always)]
    #[must_use]
    pub fn cntckdiv_3(&mut self) -> Cntckdiv3W<St1actlSpec> {
        Cntckdiv3W::new(self, 3)
    }
    #[doc = "Bits 9:15 - Rising edge dead-time value configure"]
    #[inline(always)]
    #[must_use]
    pub fn dtrcfg_15_9(&mut self) -> Dtrcfg15_9W<St1actlSpec> {
        Dtrcfg15_9W::new(self, 9)
    }
    #[doc = "Bits 25:31 - Falling edge dead-time value configure"]
    #[inline(always)]
    #[must_use]
    pub fn dtfcfg_15_9(&mut self) -> Dtfcfg15_9W<St1actlSpec> {
        Dtfcfg15_9W::new(self, 25)
    }
}
#[doc = "SHRTIMER Slave_TIMERx additional control register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`st1actl::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`st1actl::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct St1actlSpec;
impl crate::RegisterSpec for St1actlSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`st1actl::R`](R) reader structure"]
impl crate::Readable for St1actlSpec {}
#[doc = "`write(|w| ..)` method takes [`st1actl::W`](W) writer structure"]
impl crate::Writable for St1actlSpec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets ST1ACTL to value 0"]
impl crate::Resettable for St1actlSpec {
    const RESET_VALUE: u32 = 0;
}
