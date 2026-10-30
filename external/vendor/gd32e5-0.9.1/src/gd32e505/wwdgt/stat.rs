#[doc = "Register `STAT` reader"]
pub type R = crate::R<StatSpec>;
#[doc = "Register `STAT` writer"]
pub type W = crate::W<StatSpec>;
#[doc = "Early wakeup interrupt flag\n\nValue on reset: 0"]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Ewifr {
    #[doc = "1: The EWI Interrupt Service Routine has been triggered"]
    Pending = 1,
    #[doc = "0: The EWI Interrupt Service Routine has been serviced"]
    Finished = 0,
}
impl From<Ewifr> for bool {
    #[inline(always)]
    fn from(variant: Ewifr) -> Self {
        variant as u8 != 0
    }
}
#[doc = "Field `EWIF` reader - Early wakeup interrupt flag"]
pub type EwifR = crate::BitReader<Ewifr>;
impl EwifR {
    #[doc = "Get enumerated values variant"]
    #[inline(always)]
    pub const fn variant(&self) -> Ewifr {
        match self.bits {
            true => Ewifr::Pending,
            false => Ewifr::Finished,
        }
    }
    #[doc = "The EWI Interrupt Service Routine has been triggered"]
    #[inline(always)]
    pub fn is_pending(&self) -> bool {
        *self == Ewifr::Pending
    }
    #[doc = "The EWI Interrupt Service Routine has been serviced"]
    #[inline(always)]
    pub fn is_finished(&self) -> bool {
        *self == Ewifr::Finished
    }
}
#[doc = "Early wakeup interrupt flag\n\nValue on reset: 0"]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum EwifwWO {
    #[doc = "0: The EWI Interrupt Service Routine has been serviced"]
    Finished = 0,
}
impl From<EwifwWO> for bool {
    #[inline(always)]
    fn from(variant: EwifwWO) -> Self {
        variant as u8 != 0
    }
}
#[doc = "Field `EWIF` writer - Early wakeup interrupt flag"]
pub type EwifW<'a, REG> = crate::BitWriter<'a, REG, EwifwWO>;
impl<'a, REG> EwifW<'a, REG>
where
    REG: crate::Writable + crate::RegisterSpec,
{
    #[doc = "The EWI Interrupt Service Routine has been serviced"]
    #[inline(always)]
    pub fn finished(self) -> &'a mut crate::W<REG> {
        self.variant(EwifwWO::Finished)
    }
}
impl R {
    #[doc = "Bit 0 - Early wakeup interrupt flag"]
    #[inline(always)]
    pub fn ewif(&self) -> EwifR {
        EwifR::new((self.bits & 1) != 0)
    }
}
impl W {
    #[doc = "Bit 0 - Early wakeup interrupt flag"]
    #[inline(always)]
    #[must_use]
    pub fn ewif(&mut self) -> EwifW<StatSpec> {
        EwifW::new(self, 0)
    }
}
#[doc = "Status register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`stat::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`stat::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct StatSpec;
impl crate::RegisterSpec for StatSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`stat::R`](R) reader structure"]
impl crate::Readable for StatSpec {}
#[doc = "`write(|w| ..)` method takes [`stat::W`](W) writer structure"]
impl crate::Writable for StatSpec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets STAT to value 0"]
impl crate::Resettable for StatSpec {
    const RESET_VALUE: u32 = 0;
}
