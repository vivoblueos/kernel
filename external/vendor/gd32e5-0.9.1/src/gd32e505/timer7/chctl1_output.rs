#[doc = "Register `CHCTL1_Output` reader"]
pub type R = crate::R<Chctl1OutputSpec>;
#[doc = "Register `CHCTL1_Output` writer"]
pub type W = crate::W<Chctl1OutputSpec>;
#[doc = "Field `CH2MS` reader - Channel 2 I/O mode selection"]
pub type Ch2msR = crate::FieldReader;
#[doc = "Field `CH2MS` writer - Channel 2 I/O mode selection"]
pub type Ch2msW<'a, REG> = crate::FieldWriter<'a, REG, 2>;
#[doc = "Field `CH2COMFEN` reader - Channel 2 output compare fast enable"]
pub type Ch2comfenR = crate::BitReader;
#[doc = "Field `CH2COMFEN` writer - Channel 2 output compare fast enable"]
pub type Ch2comfenW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `CH2COMSEN` reader - Channel 2 compare output shadow enable"]
pub type Ch2comsenR = crate::BitReader;
#[doc = "Field `CH2COMSEN` writer - Channel 2 compare output shadow enable"]
pub type Ch2comsenW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `CH2COMCTL` reader - Channel 2 compare output control"]
pub type Ch2comctlR = crate::FieldReader;
#[doc = "Field `CH2COMCTL` writer - Channel 2 compare output control"]
pub type Ch2comctlW<'a, REG> = crate::FieldWriter<'a, REG, 3>;
#[doc = "Field `CH2COMCEN` reader - Channel 2 output compare clear enable"]
pub type Ch2comcenR = crate::BitReader;
#[doc = "Field `CH2COMCEN` writer - Channel 2 output compare clear enable"]
pub type Ch2comcenW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `CH3MS` reader - Channel 3 mode selection"]
pub type Ch3msR = crate::FieldReader;
#[doc = "Field `CH3MS` writer - Channel 3 mode selection"]
pub type Ch3msW<'a, REG> = crate::FieldWriter<'a, REG, 2>;
#[doc = "Field `CH3COMFEN` reader - Channel 3 output compare fast enable"]
pub type Ch3comfenR = crate::BitReader;
#[doc = "Field `CH3COMFEN` writer - Channel 3 output compare fast enable"]
pub type Ch3comfenW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `CH3COMSEN` reader - Channel 3 output compare shadow enable"]
pub type Ch3comsenR = crate::BitReader;
#[doc = "Field `CH3COMSEN` writer - Channel 3 output compare shadow enable"]
pub type Ch3comsenW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `CH3COMCTL` reader - Channel 3 compare output control"]
pub type Ch3comctlR = crate::FieldReader;
#[doc = "Field `CH3COMCTL` writer - Channel 3 compare output control"]
pub type Ch3comctlW<'a, REG> = crate::FieldWriter<'a, REG, 3>;
#[doc = "Field `CH3COMCEN` reader - Channel 3 output compare clear enable"]
pub type Ch3comcenR = crate::BitReader;
#[doc = "Field `CH3COMCEN` writer - Channel 3 output compare clear enable"]
pub type Ch3comcenW<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bits 0:1 - Channel 2 I/O mode selection"]
    #[inline(always)]
    pub fn ch2ms(&self) -> Ch2msR {
        Ch2msR::new((self.bits & 3) as u8)
    }
    #[doc = "Bit 2 - Channel 2 output compare fast enable"]
    #[inline(always)]
    pub fn ch2comfen(&self) -> Ch2comfenR {
        Ch2comfenR::new(((self.bits >> 2) & 1) != 0)
    }
    #[doc = "Bit 3 - Channel 2 compare output shadow enable"]
    #[inline(always)]
    pub fn ch2comsen(&self) -> Ch2comsenR {
        Ch2comsenR::new(((self.bits >> 3) & 1) != 0)
    }
    #[doc = "Bits 4:6 - Channel 2 compare output control"]
    #[inline(always)]
    pub fn ch2comctl(&self) -> Ch2comctlR {
        Ch2comctlR::new(((self.bits >> 4) & 7) as u8)
    }
    #[doc = "Bit 7 - Channel 2 output compare clear enable"]
    #[inline(always)]
    pub fn ch2comcen(&self) -> Ch2comcenR {
        Ch2comcenR::new(((self.bits >> 7) & 1) != 0)
    }
    #[doc = "Bits 8:9 - Channel 3 mode selection"]
    #[inline(always)]
    pub fn ch3ms(&self) -> Ch3msR {
        Ch3msR::new(((self.bits >> 8) & 3) as u8)
    }
    #[doc = "Bit 10 - Channel 3 output compare fast enable"]
    #[inline(always)]
    pub fn ch3comfen(&self) -> Ch3comfenR {
        Ch3comfenR::new(((self.bits >> 10) & 1) != 0)
    }
    #[doc = "Bit 11 - Channel 3 output compare shadow enable"]
    #[inline(always)]
    pub fn ch3comsen(&self) -> Ch3comsenR {
        Ch3comsenR::new(((self.bits >> 11) & 1) != 0)
    }
    #[doc = "Bits 12:14 - Channel 3 compare output control"]
    #[inline(always)]
    pub fn ch3comctl(&self) -> Ch3comctlR {
        Ch3comctlR::new(((self.bits >> 12) & 7) as u8)
    }
    #[doc = "Bit 15 - Channel 3 output compare clear enable"]
    #[inline(always)]
    pub fn ch3comcen(&self) -> Ch3comcenR {
        Ch3comcenR::new(((self.bits >> 15) & 1) != 0)
    }
}
impl W {
    #[doc = "Bits 0:1 - Channel 2 I/O mode selection"]
    #[inline(always)]
    #[must_use]
    pub fn ch2ms(&mut self) -> Ch2msW<Chctl1OutputSpec> {
        Ch2msW::new(self, 0)
    }
    #[doc = "Bit 2 - Channel 2 output compare fast enable"]
    #[inline(always)]
    #[must_use]
    pub fn ch2comfen(&mut self) -> Ch2comfenW<Chctl1OutputSpec> {
        Ch2comfenW::new(self, 2)
    }
    #[doc = "Bit 3 - Channel 2 compare output shadow enable"]
    #[inline(always)]
    #[must_use]
    pub fn ch2comsen(&mut self) -> Ch2comsenW<Chctl1OutputSpec> {
        Ch2comsenW::new(self, 3)
    }
    #[doc = "Bits 4:6 - Channel 2 compare output control"]
    #[inline(always)]
    #[must_use]
    pub fn ch2comctl(&mut self) -> Ch2comctlW<Chctl1OutputSpec> {
        Ch2comctlW::new(self, 4)
    }
    #[doc = "Bit 7 - Channel 2 output compare clear enable"]
    #[inline(always)]
    #[must_use]
    pub fn ch2comcen(&mut self) -> Ch2comcenW<Chctl1OutputSpec> {
        Ch2comcenW::new(self, 7)
    }
    #[doc = "Bits 8:9 - Channel 3 mode selection"]
    #[inline(always)]
    #[must_use]
    pub fn ch3ms(&mut self) -> Ch3msW<Chctl1OutputSpec> {
        Ch3msW::new(self, 8)
    }
    #[doc = "Bit 10 - Channel 3 output compare fast enable"]
    #[inline(always)]
    #[must_use]
    pub fn ch3comfen(&mut self) -> Ch3comfenW<Chctl1OutputSpec> {
        Ch3comfenW::new(self, 10)
    }
    #[doc = "Bit 11 - Channel 3 output compare shadow enable"]
    #[inline(always)]
    #[must_use]
    pub fn ch3comsen(&mut self) -> Ch3comsenW<Chctl1OutputSpec> {
        Ch3comsenW::new(self, 11)
    }
    #[doc = "Bits 12:14 - Channel 3 compare output control"]
    #[inline(always)]
    #[must_use]
    pub fn ch3comctl(&mut self) -> Ch3comctlW<Chctl1OutputSpec> {
        Ch3comctlW::new(self, 12)
    }
    #[doc = "Bit 15 - Channel 3 output compare clear enable"]
    #[inline(always)]
    #[must_use]
    pub fn ch3comcen(&mut self) -> Ch3comcenW<Chctl1OutputSpec> {
        Ch3comcenW::new(self, 15)
    }
}
#[doc = "Channel control register 1 (output mode)\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`chctl1_output::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`chctl1_output::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct Chctl1OutputSpec;
impl crate::RegisterSpec for Chctl1OutputSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`chctl1_output::R`](R) reader structure"]
impl crate::Readable for Chctl1OutputSpec {}
#[doc = "`write(|w| ..)` method takes [`chctl1_output::W`](W) writer structure"]
impl crate::Writable for Chctl1OutputSpec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets CHCTL1_Output to value 0"]
impl crate::Resettable for Chctl1OutputSpec {
    const RESET_VALUE: u32 = 0;
}
