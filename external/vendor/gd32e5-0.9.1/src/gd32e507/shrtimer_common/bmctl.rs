#[doc = "Register `BMCTL` reader"]
pub type R = crate::R<BmctlSpec>;
#[doc = "Register `BMCTL` writer"]
pub type W = crate::W<BmctlSpec>;
#[doc = "Field `BMEN` reader - Bunch mode enable"]
pub type BmenR = crate::BitReader;
#[doc = "Field `BMEN` writer - Bunch mode enable"]
pub type BmenW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `BMCTN` reader - Continuous mode in bunch mode"]
pub type BmctnR = crate::BitReader;
#[doc = "Field `BMCTN` writer - Continuous mode in bunch mode"]
pub type BmctnW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `BMCLKS` reader - Bunch mode clock source"]
pub type BmclksR = crate::FieldReader;
#[doc = "Field `BMCLKS` writer - Bunch mode clock source"]
pub type BmclksW<'a, REG> = crate::FieldWriter<'a, REG, 4>;
#[doc = "Field `BMPSC` reader - Bunch mode clock division"]
pub type BmpscR = crate::FieldReader;
#[doc = "Field `BMPSC` writer - Bunch mode clock division"]
pub type BmpscW<'a, REG> = crate::FieldWriter<'a, REG, 4>;
#[doc = "Field `BMSE` reader - Bunch mode shadow enable"]
pub type BmseR = crate::BitReader;
#[doc = "Field `BMSE` writer - Bunch mode shadow enable"]
pub type BmseW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `BMMT` reader - Master_TIMER bunch mode"]
pub type BmmtR = crate::BitReader;
#[doc = "Field `BMMT` writer - Master_TIMER bunch mode"]
pub type BmmtW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `BMST0` reader - Slave_TIMER0 bunch mode"]
pub type Bmst0R = crate::BitReader;
#[doc = "Field `BMST0` writer - Slave_TIMER0 bunch mode"]
pub type Bmst0W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `BMST1` reader - Slave_TIMER1 bunch mode"]
pub type Bmst1R = crate::BitReader;
#[doc = "Field `BMST1` writer - Slave_TIMER1 bunch mode"]
pub type Bmst1W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `BMST2` reader - Slave_TIMER2 bunch mode"]
pub type Bmst2R = crate::BitReader;
#[doc = "Field `BMST2` writer - Slave_TIMER2 bunch mode"]
pub type Bmst2W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `BMST3` reader - Slave_TIMER3 bunch mode"]
pub type Bmst3R = crate::BitReader;
#[doc = "Field `BMST3` writer - Slave_TIMER3 bunch mode"]
pub type Bmst3W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `BMST4` reader - Slave_TIMER4 bunch mode"]
pub type Bmst4R = crate::BitReader;
#[doc = "Field `BMST4` writer - Slave_TIMER4 bunch mode"]
pub type Bmst4W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `BMOPTF` reader - Bunch mode operating flag"]
pub type BmoptfR = crate::BitReader;
#[doc = "Field `BMOPTF` writer - Bunch mode operating flag"]
pub type BmoptfW<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 0 - Bunch mode enable"]
    #[inline(always)]
    pub fn bmen(&self) -> BmenR {
        BmenR::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - Continuous mode in bunch mode"]
    #[inline(always)]
    pub fn bmctn(&self) -> BmctnR {
        BmctnR::new(((self.bits >> 1) & 1) != 0)
    }
    #[doc = "Bits 2:5 - Bunch mode clock source"]
    #[inline(always)]
    pub fn bmclks(&self) -> BmclksR {
        BmclksR::new(((self.bits >> 2) & 0x0f) as u8)
    }
    #[doc = "Bits 6:9 - Bunch mode clock division"]
    #[inline(always)]
    pub fn bmpsc(&self) -> BmpscR {
        BmpscR::new(((self.bits >> 6) & 0x0f) as u8)
    }
    #[doc = "Bit 10 - Bunch mode shadow enable"]
    #[inline(always)]
    pub fn bmse(&self) -> BmseR {
        BmseR::new(((self.bits >> 10) & 1) != 0)
    }
    #[doc = "Bit 16 - Master_TIMER bunch mode"]
    #[inline(always)]
    pub fn bmmt(&self) -> BmmtR {
        BmmtR::new(((self.bits >> 16) & 1) != 0)
    }
    #[doc = "Bit 17 - Slave_TIMER0 bunch mode"]
    #[inline(always)]
    pub fn bmst0(&self) -> Bmst0R {
        Bmst0R::new(((self.bits >> 17) & 1) != 0)
    }
    #[doc = "Bit 18 - Slave_TIMER1 bunch mode"]
    #[inline(always)]
    pub fn bmst1(&self) -> Bmst1R {
        Bmst1R::new(((self.bits >> 18) & 1) != 0)
    }
    #[doc = "Bit 19 - Slave_TIMER2 bunch mode"]
    #[inline(always)]
    pub fn bmst2(&self) -> Bmst2R {
        Bmst2R::new(((self.bits >> 19) & 1) != 0)
    }
    #[doc = "Bit 20 - Slave_TIMER3 bunch mode"]
    #[inline(always)]
    pub fn bmst3(&self) -> Bmst3R {
        Bmst3R::new(((self.bits >> 20) & 1) != 0)
    }
    #[doc = "Bit 21 - Slave_TIMER4 bunch mode"]
    #[inline(always)]
    pub fn bmst4(&self) -> Bmst4R {
        Bmst4R::new(((self.bits >> 21) & 1) != 0)
    }
    #[doc = "Bit 31 - Bunch mode operating flag"]
    #[inline(always)]
    pub fn bmoptf(&self) -> BmoptfR {
        BmoptfR::new(((self.bits >> 31) & 1) != 0)
    }
}
impl W {
    #[doc = "Bit 0 - Bunch mode enable"]
    #[inline(always)]
    #[must_use]
    pub fn bmen(&mut self) -> BmenW<BmctlSpec> {
        BmenW::new(self, 0)
    }
    #[doc = "Bit 1 - Continuous mode in bunch mode"]
    #[inline(always)]
    #[must_use]
    pub fn bmctn(&mut self) -> BmctnW<BmctlSpec> {
        BmctnW::new(self, 1)
    }
    #[doc = "Bits 2:5 - Bunch mode clock source"]
    #[inline(always)]
    #[must_use]
    pub fn bmclks(&mut self) -> BmclksW<BmctlSpec> {
        BmclksW::new(self, 2)
    }
    #[doc = "Bits 6:9 - Bunch mode clock division"]
    #[inline(always)]
    #[must_use]
    pub fn bmpsc(&mut self) -> BmpscW<BmctlSpec> {
        BmpscW::new(self, 6)
    }
    #[doc = "Bit 10 - Bunch mode shadow enable"]
    #[inline(always)]
    #[must_use]
    pub fn bmse(&mut self) -> BmseW<BmctlSpec> {
        BmseW::new(self, 10)
    }
    #[doc = "Bit 16 - Master_TIMER bunch mode"]
    #[inline(always)]
    #[must_use]
    pub fn bmmt(&mut self) -> BmmtW<BmctlSpec> {
        BmmtW::new(self, 16)
    }
    #[doc = "Bit 17 - Slave_TIMER0 bunch mode"]
    #[inline(always)]
    #[must_use]
    pub fn bmst0(&mut self) -> Bmst0W<BmctlSpec> {
        Bmst0W::new(self, 17)
    }
    #[doc = "Bit 18 - Slave_TIMER1 bunch mode"]
    #[inline(always)]
    #[must_use]
    pub fn bmst1(&mut self) -> Bmst1W<BmctlSpec> {
        Bmst1W::new(self, 18)
    }
    #[doc = "Bit 19 - Slave_TIMER2 bunch mode"]
    #[inline(always)]
    #[must_use]
    pub fn bmst2(&mut self) -> Bmst2W<BmctlSpec> {
        Bmst2W::new(self, 19)
    }
    #[doc = "Bit 20 - Slave_TIMER3 bunch mode"]
    #[inline(always)]
    #[must_use]
    pub fn bmst3(&mut self) -> Bmst3W<BmctlSpec> {
        Bmst3W::new(self, 20)
    }
    #[doc = "Bit 21 - Slave_TIMER4 bunch mode"]
    #[inline(always)]
    #[must_use]
    pub fn bmst4(&mut self) -> Bmst4W<BmctlSpec> {
        Bmst4W::new(self, 21)
    }
    #[doc = "Bit 31 - Bunch mode operating flag"]
    #[inline(always)]
    #[must_use]
    pub fn bmoptf(&mut self) -> BmoptfW<BmctlSpec> {
        BmoptfW::new(self, 31)
    }
}
#[doc = "SHRTIMER bunch mode control register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`bmctl::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`bmctl::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct BmctlSpec;
impl crate::RegisterSpec for BmctlSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`bmctl::R`](R) reader structure"]
impl crate::Readable for BmctlSpec {}
#[doc = "`write(|w| ..)` method takes [`bmctl::W`](W) writer structure"]
impl crate::Writable for BmctlSpec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets BMCTL to value 0"]
impl crate::Resettable for BmctlSpec {
    const RESET_VALUE: u32 = 0;
}
