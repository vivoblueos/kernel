#[doc = "Register `CFG` reader"]
pub type R = crate::R<CfgSpec>;
#[doc = "Register `CFG` writer"]
pub type W = crate::W<CfgSpec>;
#[doc = "Field `WIN` reader - 7-bit window value"]
pub type WinR = crate::FieldReader;
#[doc = "Field `WIN` writer - 7-bit window value"]
pub type WinW<'a, REG> = crate::FieldWriterSafe<'a, REG, 7>;
#[doc = "Prescaler\n\nValue on reset: 0"]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u8)]
pub enum Psc {
    #[doc = "0: Counter clock (PCLK1 div 4096) div 1"]
    Div1 = 0,
    #[doc = "1: Counter clock (PCLK1 div 4096) div 2"]
    Div2 = 1,
    #[doc = "2: Counter clock (PCLK1 div 4096) div 4"]
    Div4 = 2,
    #[doc = "3: Counter clock (PCLK1 div 4096) div 8"]
    Div8 = 3,
}
impl From<Psc> for u8 {
    #[inline(always)]
    fn from(variant: Psc) -> Self {
        variant as _
    }
}
impl crate::FieldSpec for Psc {
    type Ux = u8;
}
#[doc = "Field `PSC` reader - Prescaler"]
pub type PscR = crate::FieldReader<Psc>;
impl PscR {
    #[doc = "Get enumerated values variant"]
    #[inline(always)]
    pub const fn variant(&self) -> Psc {
        match self.bits {
            0 => Psc::Div1,
            1 => Psc::Div2,
            2 => Psc::Div4,
            3 => Psc::Div8,
            _ => unreachable!(),
        }
    }
    #[doc = "Counter clock (PCLK1 div 4096) div 1"]
    #[inline(always)]
    pub fn is_div1(&self) -> bool {
        *self == Psc::Div1
    }
    #[doc = "Counter clock (PCLK1 div 4096) div 2"]
    #[inline(always)]
    pub fn is_div2(&self) -> bool {
        *self == Psc::Div2
    }
    #[doc = "Counter clock (PCLK1 div 4096) div 4"]
    #[inline(always)]
    pub fn is_div4(&self) -> bool {
        *self == Psc::Div4
    }
    #[doc = "Counter clock (PCLK1 div 4096) div 8"]
    #[inline(always)]
    pub fn is_div8(&self) -> bool {
        *self == Psc::Div8
    }
}
#[doc = "Field `PSC` writer - Prescaler"]
pub type PscW<'a, REG> = crate::FieldWriterSafe<'a, REG, 2, Psc>;
impl<'a, REG> PscW<'a, REG>
where
    REG: crate::Writable + crate::RegisterSpec,
    REG::Ux: From<u8>,
{
    #[doc = "Counter clock (PCLK1 div 4096) div 1"]
    #[inline(always)]
    pub fn div1(self) -> &'a mut crate::W<REG> {
        self.variant(Psc::Div1)
    }
    #[doc = "Counter clock (PCLK1 div 4096) div 2"]
    #[inline(always)]
    pub fn div2(self) -> &'a mut crate::W<REG> {
        self.variant(Psc::Div2)
    }
    #[doc = "Counter clock (PCLK1 div 4096) div 4"]
    #[inline(always)]
    pub fn div4(self) -> &'a mut crate::W<REG> {
        self.variant(Psc::Div4)
    }
    #[doc = "Counter clock (PCLK1 div 4096) div 8"]
    #[inline(always)]
    pub fn div8(self) -> &'a mut crate::W<REG> {
        self.variant(Psc::Div8)
    }
}
#[doc = "Early wakeup interrupt\n\nValue on reset: 0"]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Ewiew {
    #[doc = "1: interrupt occurs whenever the counter reaches the value 0x40"]
    Enable = 1,
}
impl From<Ewiew> for bool {
    #[inline(always)]
    fn from(variant: Ewiew) -> Self {
        variant as u8 != 0
    }
}
#[doc = "Field `EWIE` reader - Early wakeup interrupt"]
pub type EwieR = crate::BitReader<Ewiew>;
impl EwieR {
    #[doc = "Get enumerated values variant"]
    #[inline(always)]
    pub const fn variant(&self) -> Option<Ewiew> {
        match self.bits {
            true => Some(Ewiew::Enable),
            _ => None,
        }
    }
    #[doc = "interrupt occurs whenever the counter reaches the value 0x40"]
    #[inline(always)]
    pub fn is_enable(&self) -> bool {
        *self == Ewiew::Enable
    }
}
#[doc = "Field `EWIE` writer - Early wakeup interrupt"]
pub type EwieW<'a, REG> = crate::BitWriter<'a, REG, Ewiew>;
impl<'a, REG> EwieW<'a, REG>
where
    REG: crate::Writable + crate::RegisterSpec,
{
    #[doc = "interrupt occurs whenever the counter reaches the value 0x40"]
    #[inline(always)]
    pub fn enable(self) -> &'a mut crate::W<REG> {
        self.variant(Ewiew::Enable)
    }
}
impl R {
    #[doc = "Bits 0:6 - 7-bit window value"]
    #[inline(always)]
    pub fn win(&self) -> WinR {
        WinR::new((self.bits & 0x7f) as u8)
    }
    #[doc = "Bits 7:8 - Prescaler"]
    #[inline(always)]
    pub fn psc(&self) -> PscR {
        PscR::new(((self.bits >> 7) & 3) as u8)
    }
    #[doc = "Bit 9 - Early wakeup interrupt"]
    #[inline(always)]
    pub fn ewie(&self) -> EwieR {
        EwieR::new(((self.bits >> 9) & 1) != 0)
    }
}
impl W {
    #[doc = "Bits 0:6 - 7-bit window value"]
    #[inline(always)]
    #[must_use]
    pub fn win(&mut self) -> WinW<CfgSpec> {
        WinW::new(self, 0)
    }
    #[doc = "Bits 7:8 - Prescaler"]
    #[inline(always)]
    #[must_use]
    pub fn psc(&mut self) -> PscW<CfgSpec> {
        PscW::new(self, 7)
    }
    #[doc = "Bit 9 - Early wakeup interrupt"]
    #[inline(always)]
    #[must_use]
    pub fn ewie(&mut self) -> EwieW<CfgSpec> {
        EwieW::new(self, 9)
    }
}
#[doc = "Configuration register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`cfg::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`cfg::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct CfgSpec;
impl crate::RegisterSpec for CfgSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`cfg::R`](R) reader structure"]
impl crate::Readable for CfgSpec {}
#[doc = "`write(|w| ..)` method takes [`cfg::W`](W) writer structure"]
impl crate::Writable for CfgSpec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets CFG to value 0x7f"]
impl crate::Resettable for CfgSpec {
    const RESET_VALUE: u32 = 0x7f;
}
