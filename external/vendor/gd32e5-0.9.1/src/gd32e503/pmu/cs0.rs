#[doc = "Register `CS0` reader"]
pub type R = crate::R<Cs0Spec>;
#[doc = "Register `CS0` writer"]
pub type W = crate::W<Cs0Spec>;
#[doc = "Field `WUF` reader - Wakeup flag"]
pub type WufR = crate::BitReader;
#[doc = "Field `STBF` reader - Standby flag"]
pub type StbfR = crate::BitReader;
#[doc = "Field `LVDF` reader - Low Voltage Detector Status Flag"]
pub type LvdfR = crate::BitReader;
#[doc = "Field `WUPEN6` reader - Enable WKUP pin6"]
pub type Wupen6R = crate::BitReader;
#[doc = "Field `WUPEN6` writer - Enable WKUP pin6"]
pub type Wupen6W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `WUPEN0` reader - Enable WKUP pin0"]
pub type Wupen0R = crate::BitReader;
#[doc = "Field `WUPEN0` writer - Enable WKUP pin0"]
pub type Wupen0W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `WUPEN1` reader - Enable WKUP pin1"]
pub type Wupen1R = crate::BitReader;
#[doc = "Field `WUPEN1` writer - Enable WKUP pin1"]
pub type Wupen1W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `WUPEN2` reader - Enable WKUP pin2"]
pub type Wupen2R = crate::BitReader;
#[doc = "Field `WUPEN2` writer - Enable WKUP pin2"]
pub type Wupen2W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `WUPEN3` reader - Enable WKUP pin3"]
pub type Wupen3R = crate::BitReader;
#[doc = "Field `WUPEN3` writer - Enable WKUP pin3"]
pub type Wupen3W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `WUPEN4` reader - Enable WKUP pin4"]
pub type Wupen4R = crate::BitReader;
#[doc = "Field `WUPEN4` writer - Enable WKUP pin4"]
pub type Wupen4W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `WUPEN5` reader - Enable WKUP pin5"]
pub type Wupen5R = crate::BitReader;
#[doc = "Field `WUPEN5` writer - Enable WKUP pin5"]
pub type Wupen5W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `WUPEN7` reader - Enable WKUP Pin7(PF8)"]
pub type Wupen7R = crate::BitReader;
#[doc = "Field `WUPEN7` writer - Enable WKUP Pin7(PF8)"]
pub type Wupen7W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `HDRF` reader - High-driver ready flag"]
pub type HdrfR = crate::BitReader;
#[doc = "Field `HDSRF` reader - High-driver switch ready flag"]
pub type HdsrfR = crate::BitReader;
#[doc = "Field `LDRF` reader - Low-driver mode ready flag"]
pub type LdrfR = crate::FieldReader;
#[doc = "Field `LDRF` writer - Low-driver mode ready flag"]
pub type LdrfW<'a, REG> = crate::FieldWriter<'a, REG, 2>;
impl R {
    #[doc = "Bit 0 - Wakeup flag"]
    #[inline(always)]
    pub fn wuf(&self) -> WufR {
        WufR::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - Standby flag"]
    #[inline(always)]
    pub fn stbf(&self) -> StbfR {
        StbfR::new(((self.bits >> 1) & 1) != 0)
    }
    #[doc = "Bit 2 - Low Voltage Detector Status Flag"]
    #[inline(always)]
    pub fn lvdf(&self) -> LvdfR {
        LvdfR::new(((self.bits >> 2) & 1) != 0)
    }
    #[doc = "Bit 7 - Enable WKUP pin6"]
    #[inline(always)]
    pub fn wupen6(&self) -> Wupen6R {
        Wupen6R::new(((self.bits >> 7) & 1) != 0)
    }
    #[doc = "Bit 8 - Enable WKUP pin0"]
    #[inline(always)]
    pub fn wupen0(&self) -> Wupen0R {
        Wupen0R::new(((self.bits >> 8) & 1) != 0)
    }
    #[doc = "Bit 9 - Enable WKUP pin1"]
    #[inline(always)]
    pub fn wupen1(&self) -> Wupen1R {
        Wupen1R::new(((self.bits >> 9) & 1) != 0)
    }
    #[doc = "Bit 10 - Enable WKUP pin2"]
    #[inline(always)]
    pub fn wupen2(&self) -> Wupen2R {
        Wupen2R::new(((self.bits >> 10) & 1) != 0)
    }
    #[doc = "Bit 11 - Enable WKUP pin3"]
    #[inline(always)]
    pub fn wupen3(&self) -> Wupen3R {
        Wupen3R::new(((self.bits >> 11) & 1) != 0)
    }
    #[doc = "Bit 12 - Enable WKUP pin4"]
    #[inline(always)]
    pub fn wupen4(&self) -> Wupen4R {
        Wupen4R::new(((self.bits >> 12) & 1) != 0)
    }
    #[doc = "Bit 13 - Enable WKUP pin5"]
    #[inline(always)]
    pub fn wupen5(&self) -> Wupen5R {
        Wupen5R::new(((self.bits >> 13) & 1) != 0)
    }
    #[doc = "Bit 15 - Enable WKUP Pin7(PF8)"]
    #[inline(always)]
    pub fn wupen7(&self) -> Wupen7R {
        Wupen7R::new(((self.bits >> 15) & 1) != 0)
    }
    #[doc = "Bit 16 - High-driver ready flag"]
    #[inline(always)]
    pub fn hdrf(&self) -> HdrfR {
        HdrfR::new(((self.bits >> 16) & 1) != 0)
    }
    #[doc = "Bit 17 - High-driver switch ready flag"]
    #[inline(always)]
    pub fn hdsrf(&self) -> HdsrfR {
        HdsrfR::new(((self.bits >> 17) & 1) != 0)
    }
    #[doc = "Bits 18:19 - Low-driver mode ready flag"]
    #[inline(always)]
    pub fn ldrf(&self) -> LdrfR {
        LdrfR::new(((self.bits >> 18) & 3) as u8)
    }
}
impl W {
    #[doc = "Bit 7 - Enable WKUP pin6"]
    #[inline(always)]
    #[must_use]
    pub fn wupen6(&mut self) -> Wupen6W<Cs0Spec> {
        Wupen6W::new(self, 7)
    }
    #[doc = "Bit 8 - Enable WKUP pin0"]
    #[inline(always)]
    #[must_use]
    pub fn wupen0(&mut self) -> Wupen0W<Cs0Spec> {
        Wupen0W::new(self, 8)
    }
    #[doc = "Bit 9 - Enable WKUP pin1"]
    #[inline(always)]
    #[must_use]
    pub fn wupen1(&mut self) -> Wupen1W<Cs0Spec> {
        Wupen1W::new(self, 9)
    }
    #[doc = "Bit 10 - Enable WKUP pin2"]
    #[inline(always)]
    #[must_use]
    pub fn wupen2(&mut self) -> Wupen2W<Cs0Spec> {
        Wupen2W::new(self, 10)
    }
    #[doc = "Bit 11 - Enable WKUP pin3"]
    #[inline(always)]
    #[must_use]
    pub fn wupen3(&mut self) -> Wupen3W<Cs0Spec> {
        Wupen3W::new(self, 11)
    }
    #[doc = "Bit 12 - Enable WKUP pin4"]
    #[inline(always)]
    #[must_use]
    pub fn wupen4(&mut self) -> Wupen4W<Cs0Spec> {
        Wupen4W::new(self, 12)
    }
    #[doc = "Bit 13 - Enable WKUP pin5"]
    #[inline(always)]
    #[must_use]
    pub fn wupen5(&mut self) -> Wupen5W<Cs0Spec> {
        Wupen5W::new(self, 13)
    }
    #[doc = "Bit 15 - Enable WKUP Pin7(PF8)"]
    #[inline(always)]
    #[must_use]
    pub fn wupen7(&mut self) -> Wupen7W<Cs0Spec> {
        Wupen7W::new(self, 15)
    }
    #[doc = "Bits 18:19 - Low-driver mode ready flag"]
    #[inline(always)]
    #[must_use]
    pub fn ldrf(&mut self) -> LdrfW<Cs0Spec> {
        LdrfW::new(self, 18)
    }
}
#[doc = "power control/status register 0\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`cs0::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`cs0::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct Cs0Spec;
impl crate::RegisterSpec for Cs0Spec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`cs0::R`](R) reader structure"]
impl crate::Readable for Cs0Spec {}
#[doc = "`write(|w| ..)` method takes [`cs0::W`](W) writer structure"]
impl crate::Writable for Cs0Spec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets CS0 to value 0"]
impl crate::Resettable for Cs0Spec {
    const RESET_VALUE: u32 = 0;
}
