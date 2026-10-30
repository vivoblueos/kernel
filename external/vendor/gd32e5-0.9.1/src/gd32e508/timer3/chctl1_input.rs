#[doc = "Register `CHCTL1_Input` reader"]
pub type R = crate::R<Chctl1InputSpec>;
#[doc = "Register `CHCTL1_Input` writer"]
pub type W = crate::W<Chctl1InputSpec>;
#[doc = "Field `CH2MS` reader - Channel 2 mode selection"]
pub type Ch2msR = crate::FieldReader;
#[doc = "Field `CH2MS` writer - Channel 2 mode selection"]
pub type Ch2msW<'a, REG> = crate::FieldWriter<'a, REG, 2>;
#[doc = "Field `CH2CAPPSC` reader - Channel 2 input capture prescaler"]
pub type Ch2cappscR = crate::FieldReader;
#[doc = "Field `CH2CAPPSC` writer - Channel 2 input capture prescaler"]
pub type Ch2cappscW<'a, REG> = crate::FieldWriter<'a, REG, 2>;
#[doc = "Field `CH2CAPFLT` reader - Channel 2 input capture filter control"]
pub type Ch2capfltR = crate::FieldReader;
#[doc = "Field `CH2CAPFLT` writer - Channel 2 input capture filter control"]
pub type Ch2capfltW<'a, REG> = crate::FieldWriter<'a, REG, 4>;
#[doc = "Field `CH3MS` reader - Channel 3 mode selection"]
pub type Ch3msR = crate::FieldReader;
#[doc = "Field `CH3MS` writer - Channel 3 mode selection"]
pub type Ch3msW<'a, REG> = crate::FieldWriter<'a, REG, 2>;
#[doc = "Field `CH3CAPPSC` reader - Channel 3 input capture prescaler"]
pub type Ch3cappscR = crate::FieldReader;
#[doc = "Field `CH3CAPPSC` writer - Channel 3 input capture prescaler"]
pub type Ch3cappscW<'a, REG> = crate::FieldWriter<'a, REG, 2>;
#[doc = "Field `CH3CAPFLT` reader - Channel 3 input capture filter control"]
pub type Ch3capfltR = crate::FieldReader;
#[doc = "Field `CH3CAPFLT` writer - Channel 3 input capture filter control"]
pub type Ch3capfltW<'a, REG> = crate::FieldWriter<'a, REG, 4>;
impl R {
    #[doc = "Bits 0:1 - Channel 2 mode selection"]
    #[inline(always)]
    pub fn ch2ms(&self) -> Ch2msR {
        Ch2msR::new((self.bits & 3) as u8)
    }
    #[doc = "Bits 2:3 - Channel 2 input capture prescaler"]
    #[inline(always)]
    pub fn ch2cappsc(&self) -> Ch2cappscR {
        Ch2cappscR::new(((self.bits >> 2) & 3) as u8)
    }
    #[doc = "Bits 4:7 - Channel 2 input capture filter control"]
    #[inline(always)]
    pub fn ch2capflt(&self) -> Ch2capfltR {
        Ch2capfltR::new(((self.bits >> 4) & 0x0f) as u8)
    }
    #[doc = "Bits 8:9 - Channel 3 mode selection"]
    #[inline(always)]
    pub fn ch3ms(&self) -> Ch3msR {
        Ch3msR::new(((self.bits >> 8) & 3) as u8)
    }
    #[doc = "Bits 10:11 - Channel 3 input capture prescaler"]
    #[inline(always)]
    pub fn ch3cappsc(&self) -> Ch3cappscR {
        Ch3cappscR::new(((self.bits >> 10) & 3) as u8)
    }
    #[doc = "Bits 12:15 - Channel 3 input capture filter control"]
    #[inline(always)]
    pub fn ch3capflt(&self) -> Ch3capfltR {
        Ch3capfltR::new(((self.bits >> 12) & 0x0f) as u8)
    }
}
impl W {
    #[doc = "Bits 0:1 - Channel 2 mode selection"]
    #[inline(always)]
    #[must_use]
    pub fn ch2ms(&mut self) -> Ch2msW<Chctl1InputSpec> {
        Ch2msW::new(self, 0)
    }
    #[doc = "Bits 2:3 - Channel 2 input capture prescaler"]
    #[inline(always)]
    #[must_use]
    pub fn ch2cappsc(&mut self) -> Ch2cappscW<Chctl1InputSpec> {
        Ch2cappscW::new(self, 2)
    }
    #[doc = "Bits 4:7 - Channel 2 input capture filter control"]
    #[inline(always)]
    #[must_use]
    pub fn ch2capflt(&mut self) -> Ch2capfltW<Chctl1InputSpec> {
        Ch2capfltW::new(self, 4)
    }
    #[doc = "Bits 8:9 - Channel 3 mode selection"]
    #[inline(always)]
    #[must_use]
    pub fn ch3ms(&mut self) -> Ch3msW<Chctl1InputSpec> {
        Ch3msW::new(self, 8)
    }
    #[doc = "Bits 10:11 - Channel 3 input capture prescaler"]
    #[inline(always)]
    #[must_use]
    pub fn ch3cappsc(&mut self) -> Ch3cappscW<Chctl1InputSpec> {
        Ch3cappscW::new(self, 10)
    }
    #[doc = "Bits 12:15 - Channel 3 input capture filter control"]
    #[inline(always)]
    #[must_use]
    pub fn ch3capflt(&mut self) -> Ch3capfltW<Chctl1InputSpec> {
        Ch3capfltW::new(self, 12)
    }
}
#[doc = "Channel control register 1 (input mode)\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`chctl1_input::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`chctl1_input::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct Chctl1InputSpec;
impl crate::RegisterSpec for Chctl1InputSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`chctl1_input::R`](R) reader structure"]
impl crate::Readable for Chctl1InputSpec {}
#[doc = "`write(|w| ..)` method takes [`chctl1_input::W`](W) writer structure"]
impl crate::Writable for Chctl1InputSpec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets CHCTL1_Input to value 0"]
impl crate::Resettable for Chctl1InputSpec {
    const RESET_VALUE: u32 = 0;
}
