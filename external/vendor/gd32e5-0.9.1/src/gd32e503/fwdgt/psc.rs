#[doc = "Register `PSC` reader"]
pub type R = crate::R<PscSpec>;
#[doc = "Register `PSC` writer"]
pub type W = crate::W<PscSpec>;
#[doc = "Free watchdog timer prescaler selection\n\nValue on reset: 0"]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u8)]
pub enum Psc {
    #[doc = "0: Divider /4"]
    DivideBy4 = 0,
    #[doc = "1: Divider /8"]
    DivideBy8 = 1,
    #[doc = "2: Divider /16"]
    DivideBy16 = 2,
    #[doc = "3: Divider /32"]
    DivideBy32 = 3,
    #[doc = "4: Divider /64"]
    DivideBy64 = 4,
    #[doc = "5: Divider /128"]
    DivideBy128 = 5,
    #[doc = "6: Divider /256"]
    DivideBy256 = 6,
    #[doc = "7: Divider /256"]
    DivideBy256bis = 7,
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
#[doc = "Field `PSC` reader - Free watchdog timer prescaler selection"]
pub type PscR = crate::FieldReader<Psc>;
impl PscR {
    #[doc = "Get enumerated values variant"]
    #[inline(always)]
    pub const fn variant(&self) -> Psc {
        match self.bits {
            0 => Psc::DivideBy4,
            1 => Psc::DivideBy8,
            2 => Psc::DivideBy16,
            3 => Psc::DivideBy32,
            4 => Psc::DivideBy64,
            5 => Psc::DivideBy128,
            6 => Psc::DivideBy256,
            7 => Psc::DivideBy256bis,
            _ => unreachable!(),
        }
    }
    #[doc = "Divider /4"]
    #[inline(always)]
    pub fn is_divide_by4(&self) -> bool {
        *self == Psc::DivideBy4
    }
    #[doc = "Divider /8"]
    #[inline(always)]
    pub fn is_divide_by8(&self) -> bool {
        *self == Psc::DivideBy8
    }
    #[doc = "Divider /16"]
    #[inline(always)]
    pub fn is_divide_by16(&self) -> bool {
        *self == Psc::DivideBy16
    }
    #[doc = "Divider /32"]
    #[inline(always)]
    pub fn is_divide_by32(&self) -> bool {
        *self == Psc::DivideBy32
    }
    #[doc = "Divider /64"]
    #[inline(always)]
    pub fn is_divide_by64(&self) -> bool {
        *self == Psc::DivideBy64
    }
    #[doc = "Divider /128"]
    #[inline(always)]
    pub fn is_divide_by128(&self) -> bool {
        *self == Psc::DivideBy128
    }
    #[doc = "Divider /256"]
    #[inline(always)]
    pub fn is_divide_by256(&self) -> bool {
        *self == Psc::DivideBy256
    }
    #[doc = "Divider /256"]
    #[inline(always)]
    pub fn is_divide_by256bis(&self) -> bool {
        *self == Psc::DivideBy256bis
    }
}
#[doc = "Field `PSC` writer - Free watchdog timer prescaler selection"]
pub type PscW<'a, REG> = crate::FieldWriterSafe<'a, REG, 3, Psc>;
impl<'a, REG> PscW<'a, REG>
where
    REG: crate::Writable + crate::RegisterSpec,
    REG::Ux: From<u8>,
{
    #[doc = "Divider /4"]
    #[inline(always)]
    pub fn divide_by4(self) -> &'a mut crate::W<REG> {
        self.variant(Psc::DivideBy4)
    }
    #[doc = "Divider /8"]
    #[inline(always)]
    pub fn divide_by8(self) -> &'a mut crate::W<REG> {
        self.variant(Psc::DivideBy8)
    }
    #[doc = "Divider /16"]
    #[inline(always)]
    pub fn divide_by16(self) -> &'a mut crate::W<REG> {
        self.variant(Psc::DivideBy16)
    }
    #[doc = "Divider /32"]
    #[inline(always)]
    pub fn divide_by32(self) -> &'a mut crate::W<REG> {
        self.variant(Psc::DivideBy32)
    }
    #[doc = "Divider /64"]
    #[inline(always)]
    pub fn divide_by64(self) -> &'a mut crate::W<REG> {
        self.variant(Psc::DivideBy64)
    }
    #[doc = "Divider /128"]
    #[inline(always)]
    pub fn divide_by128(self) -> &'a mut crate::W<REG> {
        self.variant(Psc::DivideBy128)
    }
    #[doc = "Divider /256"]
    #[inline(always)]
    pub fn divide_by256(self) -> &'a mut crate::W<REG> {
        self.variant(Psc::DivideBy256)
    }
    #[doc = "Divider /256"]
    #[inline(always)]
    pub fn divide_by256bis(self) -> &'a mut crate::W<REG> {
        self.variant(Psc::DivideBy256bis)
    }
}
impl R {
    #[doc = "Bits 0:2 - Free watchdog timer prescaler selection"]
    #[inline(always)]
    pub fn psc(&self) -> PscR {
        PscR::new((self.bits & 7) as u8)
    }
}
impl W {
    #[doc = "Bits 0:2 - Free watchdog timer prescaler selection"]
    #[inline(always)]
    #[must_use]
    pub fn psc(&mut self) -> PscW<PscSpec> {
        PscW::new(self, 0)
    }
}
#[doc = "Prescaler register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`psc::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`psc::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct PscSpec;
impl crate::RegisterSpec for PscSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`psc::R`](R) reader structure"]
impl crate::Readable for PscSpec {}
#[doc = "`write(|w| ..)` method takes [`psc::W`](W) writer structure"]
impl crate::Writable for PscSpec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets PSC to value 0"]
impl crate::Resettable for PscSpec {
    const RESET_VALUE: u32 = 0;
}
