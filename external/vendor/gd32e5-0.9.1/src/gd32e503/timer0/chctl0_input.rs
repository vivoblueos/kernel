#[doc = "Register `CHCTL0_Input` reader"]
pub type R = crate::R<Chctl0InputSpec>;
#[doc = "Register `CHCTL0_Input` writer"]
pub type W = crate::W<Chctl0InputSpec>;
#[doc = "Channel 0 mode selection\n\nValue on reset: 0"]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u8)]
pub enum Ch0ms {
    #[doc = "0: Channel is configured as output"]
    Output = 0,
    #[doc = "1: Channel is configured as input, ISx is connected to CI0FEx"]
    Ci0 = 1,
    #[doc = "2: Channel is configured as input, ISx is connected to CI1FEx"]
    Ci1 = 2,
    #[doc = "3: Channel is configured as input, ISx is connected to ITS"]
    Its = 3,
}
impl From<Ch0ms> for u8 {
    #[inline(always)]
    fn from(variant: Ch0ms) -> Self {
        variant as _
    }
}
impl crate::FieldSpec for Ch0ms {
    type Ux = u8;
}
#[doc = "Field `CH0MS` reader - Channel 0 mode selection"]
pub type Ch0msR = crate::FieldReader<Ch0ms>;
impl Ch0msR {
    #[doc = "Get enumerated values variant"]
    #[inline(always)]
    pub const fn variant(&self) -> Ch0ms {
        match self.bits {
            0 => Ch0ms::Output,
            1 => Ch0ms::Ci0,
            2 => Ch0ms::Ci1,
            3 => Ch0ms::Its,
            _ => unreachable!(),
        }
    }
    #[doc = "Channel is configured as output"]
    #[inline(always)]
    pub fn is_output(&self) -> bool {
        *self == Ch0ms::Output
    }
    #[doc = "Channel is configured as input, ISx is connected to CI0FEx"]
    #[inline(always)]
    pub fn is_ci0(&self) -> bool {
        *self == Ch0ms::Ci0
    }
    #[doc = "Channel is configured as input, ISx is connected to CI1FEx"]
    #[inline(always)]
    pub fn is_ci1(&self) -> bool {
        *self == Ch0ms::Ci1
    }
    #[doc = "Channel is configured as input, ISx is connected to ITS"]
    #[inline(always)]
    pub fn is_its(&self) -> bool {
        *self == Ch0ms::Its
    }
}
#[doc = "Field `CH0MS` writer - Channel 0 mode selection"]
pub type Ch0msW<'a, REG> = crate::FieldWriterSafe<'a, REG, 2, Ch0ms>;
impl<'a, REG> Ch0msW<'a, REG>
where
    REG: crate::Writable + crate::RegisterSpec,
    REG::Ux: From<u8>,
{
    #[doc = "Channel is configured as output"]
    #[inline(always)]
    pub fn output(self) -> &'a mut crate::W<REG> {
        self.variant(Ch0ms::Output)
    }
    #[doc = "Channel is configured as input, ISx is connected to CI0FEx"]
    #[inline(always)]
    pub fn ci0(self) -> &'a mut crate::W<REG> {
        self.variant(Ch0ms::Ci0)
    }
    #[doc = "Channel is configured as input, ISx is connected to CI1FEx"]
    #[inline(always)]
    pub fn ci1(self) -> &'a mut crate::W<REG> {
        self.variant(Ch0ms::Ci1)
    }
    #[doc = "Channel is configured as input, ISx is connected to ITS"]
    #[inline(always)]
    pub fn its(self) -> &'a mut crate::W<REG> {
        self.variant(Ch0ms::Its)
    }
}
#[doc = "Channel 0 input capture prescaler\n\nValue on reset: 0"]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u8)]
pub enum Ch0cappsc {
    #[doc = "0: Prescaler disabled, capture on every edge"]
    Div1 = 0,
    #[doc = "1: Capture every 2 edges"]
    Div2 = 1,
    #[doc = "2: Capture every 4 edges"]
    Div4 = 2,
    #[doc = "3: Capture every 8 edges"]
    Div8 = 3,
}
impl From<Ch0cappsc> for u8 {
    #[inline(always)]
    fn from(variant: Ch0cappsc) -> Self {
        variant as _
    }
}
impl crate::FieldSpec for Ch0cappsc {
    type Ux = u8;
}
#[doc = "Field `CH0CAPPSC` reader - Channel 0 input capture prescaler"]
pub type Ch0cappscR = crate::FieldReader<Ch0cappsc>;
impl Ch0cappscR {
    #[doc = "Get enumerated values variant"]
    #[inline(always)]
    pub const fn variant(&self) -> Ch0cappsc {
        match self.bits {
            0 => Ch0cappsc::Div1,
            1 => Ch0cappsc::Div2,
            2 => Ch0cappsc::Div4,
            3 => Ch0cappsc::Div8,
            _ => unreachable!(),
        }
    }
    #[doc = "Prescaler disabled, capture on every edge"]
    #[inline(always)]
    pub fn is_div1(&self) -> bool {
        *self == Ch0cappsc::Div1
    }
    #[doc = "Capture every 2 edges"]
    #[inline(always)]
    pub fn is_div2(&self) -> bool {
        *self == Ch0cappsc::Div2
    }
    #[doc = "Capture every 4 edges"]
    #[inline(always)]
    pub fn is_div4(&self) -> bool {
        *self == Ch0cappsc::Div4
    }
    #[doc = "Capture every 8 edges"]
    #[inline(always)]
    pub fn is_div8(&self) -> bool {
        *self == Ch0cappsc::Div8
    }
}
#[doc = "Field `CH0CAPPSC` writer - Channel 0 input capture prescaler"]
pub type Ch0cappscW<'a, REG> = crate::FieldWriterSafe<'a, REG, 2, Ch0cappsc>;
impl<'a, REG> Ch0cappscW<'a, REG>
where
    REG: crate::Writable + crate::RegisterSpec,
    REG::Ux: From<u8>,
{
    #[doc = "Prescaler disabled, capture on every edge"]
    #[inline(always)]
    pub fn div1(self) -> &'a mut crate::W<REG> {
        self.variant(Ch0cappsc::Div1)
    }
    #[doc = "Capture every 2 edges"]
    #[inline(always)]
    pub fn div2(self) -> &'a mut crate::W<REG> {
        self.variant(Ch0cappsc::Div2)
    }
    #[doc = "Capture every 4 edges"]
    #[inline(always)]
    pub fn div4(self) -> &'a mut crate::W<REG> {
        self.variant(Ch0cappsc::Div4)
    }
    #[doc = "Capture every 8 edges"]
    #[inline(always)]
    pub fn div8(self) -> &'a mut crate::W<REG> {
        self.variant(Ch0cappsc::Div8)
    }
}
#[doc = "Channel 0 input capture filter control\n\nValue on reset: 0"]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u8)]
pub enum Ch0capflt {
    #[doc = "0: Filter disabled. fSAMP=fDTS, N=1"]
    NoFilter = 0,
    #[doc = "1: fSAMP=fTIMER_CK, N=2"]
    TimerCkN2 = 1,
    #[doc = "2: fSAMP=fTIMER_CK, N=4"]
    TimerCkN4 = 2,
    #[doc = "3: fSAMP=fTIMER_CK, N=8"]
    TimerCkN8 = 3,
    #[doc = "4: fSAMP=fDTS/2, N=6"]
    FdtsDiv2N6 = 4,
    #[doc = "5: fSAMP=fDTS/2, N=8"]
    FdtsDiv2N8 = 5,
    #[doc = "6: fSAMP=fDTS/4, N=6"]
    FdtsDiv4N6 = 6,
    #[doc = "7: fSAMP=fDTS/4, N=8"]
    FdtsDiv4N8 = 7,
    #[doc = "8: fSAMP=fDTS/8, N=6"]
    FdtsDiv8N6 = 8,
    #[doc = "9: fSAMP=fDTS/8, N=8"]
    FdtsDiv8N8 = 9,
    #[doc = "10: fSAMP=fDTS/16, N=5"]
    FdtsDiv16N5 = 10,
    #[doc = "11: fSAMP=fDTS/16, N=6"]
    FdtsDiv16N6 = 11,
    #[doc = "12: fSAMP=fDTS/16, N=8"]
    FdtsDiv16N8 = 12,
    #[doc = "13: fSAMP=fDTS/32, N=5"]
    FdtsDiv32N5 = 13,
    #[doc = "14: fSAMP=fDTS/32, N=6"]
    FdtsDiv32N6 = 14,
    #[doc = "15: fSAMP=fDTS/32, N=8"]
    FdtsDiv32N8 = 15,
}
impl From<Ch0capflt> for u8 {
    #[inline(always)]
    fn from(variant: Ch0capflt) -> Self {
        variant as _
    }
}
impl crate::FieldSpec for Ch0capflt {
    type Ux = u8;
}
#[doc = "Field `CH0CAPFLT` reader - Channel 0 input capture filter control"]
pub type Ch0capfltR = crate::FieldReader<Ch0capflt>;
impl Ch0capfltR {
    #[doc = "Get enumerated values variant"]
    #[inline(always)]
    pub const fn variant(&self) -> Ch0capflt {
        match self.bits {
            0 => Ch0capflt::NoFilter,
            1 => Ch0capflt::TimerCkN2,
            2 => Ch0capflt::TimerCkN4,
            3 => Ch0capflt::TimerCkN8,
            4 => Ch0capflt::FdtsDiv2N6,
            5 => Ch0capflt::FdtsDiv2N8,
            6 => Ch0capflt::FdtsDiv4N6,
            7 => Ch0capflt::FdtsDiv4N8,
            8 => Ch0capflt::FdtsDiv8N6,
            9 => Ch0capflt::FdtsDiv8N8,
            10 => Ch0capflt::FdtsDiv16N5,
            11 => Ch0capflt::FdtsDiv16N6,
            12 => Ch0capflt::FdtsDiv16N8,
            13 => Ch0capflt::FdtsDiv32N5,
            14 => Ch0capflt::FdtsDiv32N6,
            15 => Ch0capflt::FdtsDiv32N8,
            _ => unreachable!(),
        }
    }
    #[doc = "Filter disabled. fSAMP=fDTS, N=1"]
    #[inline(always)]
    pub fn is_no_filter(&self) -> bool {
        *self == Ch0capflt::NoFilter
    }
    #[doc = "fSAMP=fTIMER_CK, N=2"]
    #[inline(always)]
    pub fn is_timer_ck_n2(&self) -> bool {
        *self == Ch0capflt::TimerCkN2
    }
    #[doc = "fSAMP=fTIMER_CK, N=4"]
    #[inline(always)]
    pub fn is_timer_ck_n4(&self) -> bool {
        *self == Ch0capflt::TimerCkN4
    }
    #[doc = "fSAMP=fTIMER_CK, N=8"]
    #[inline(always)]
    pub fn is_timer_ck_n8(&self) -> bool {
        *self == Ch0capflt::TimerCkN8
    }
    #[doc = "fSAMP=fDTS/2, N=6"]
    #[inline(always)]
    pub fn is_fdts_div2_n6(&self) -> bool {
        *self == Ch0capflt::FdtsDiv2N6
    }
    #[doc = "fSAMP=fDTS/2, N=8"]
    #[inline(always)]
    pub fn is_fdts_div2_n8(&self) -> bool {
        *self == Ch0capflt::FdtsDiv2N8
    }
    #[doc = "fSAMP=fDTS/4, N=6"]
    #[inline(always)]
    pub fn is_fdts_div4_n6(&self) -> bool {
        *self == Ch0capflt::FdtsDiv4N6
    }
    #[doc = "fSAMP=fDTS/4, N=8"]
    #[inline(always)]
    pub fn is_fdts_div4_n8(&self) -> bool {
        *self == Ch0capflt::FdtsDiv4N8
    }
    #[doc = "fSAMP=fDTS/8, N=6"]
    #[inline(always)]
    pub fn is_fdts_div8_n6(&self) -> bool {
        *self == Ch0capflt::FdtsDiv8N6
    }
    #[doc = "fSAMP=fDTS/8, N=8"]
    #[inline(always)]
    pub fn is_fdts_div8_n8(&self) -> bool {
        *self == Ch0capflt::FdtsDiv8N8
    }
    #[doc = "fSAMP=fDTS/16, N=5"]
    #[inline(always)]
    pub fn is_fdts_div16_n5(&self) -> bool {
        *self == Ch0capflt::FdtsDiv16N5
    }
    #[doc = "fSAMP=fDTS/16, N=6"]
    #[inline(always)]
    pub fn is_fdts_div16_n6(&self) -> bool {
        *self == Ch0capflt::FdtsDiv16N6
    }
    #[doc = "fSAMP=fDTS/16, N=8"]
    #[inline(always)]
    pub fn is_fdts_div16_n8(&self) -> bool {
        *self == Ch0capflt::FdtsDiv16N8
    }
    #[doc = "fSAMP=fDTS/32, N=5"]
    #[inline(always)]
    pub fn is_fdts_div32_n5(&self) -> bool {
        *self == Ch0capflt::FdtsDiv32N5
    }
    #[doc = "fSAMP=fDTS/32, N=6"]
    #[inline(always)]
    pub fn is_fdts_div32_n6(&self) -> bool {
        *self == Ch0capflt::FdtsDiv32N6
    }
    #[doc = "fSAMP=fDTS/32, N=8"]
    #[inline(always)]
    pub fn is_fdts_div32_n8(&self) -> bool {
        *self == Ch0capflt::FdtsDiv32N8
    }
}
#[doc = "Field `CH0CAPFLT` writer - Channel 0 input capture filter control"]
pub type Ch0capfltW<'a, REG> = crate::FieldWriterSafe<'a, REG, 4, Ch0capflt>;
impl<'a, REG> Ch0capfltW<'a, REG>
where
    REG: crate::Writable + crate::RegisterSpec,
    REG::Ux: From<u8>,
{
    #[doc = "Filter disabled. fSAMP=fDTS, N=1"]
    #[inline(always)]
    pub fn no_filter(self) -> &'a mut crate::W<REG> {
        self.variant(Ch0capflt::NoFilter)
    }
    #[doc = "fSAMP=fTIMER_CK, N=2"]
    #[inline(always)]
    pub fn timer_ck_n2(self) -> &'a mut crate::W<REG> {
        self.variant(Ch0capflt::TimerCkN2)
    }
    #[doc = "fSAMP=fTIMER_CK, N=4"]
    #[inline(always)]
    pub fn timer_ck_n4(self) -> &'a mut crate::W<REG> {
        self.variant(Ch0capflt::TimerCkN4)
    }
    #[doc = "fSAMP=fTIMER_CK, N=8"]
    #[inline(always)]
    pub fn timer_ck_n8(self) -> &'a mut crate::W<REG> {
        self.variant(Ch0capflt::TimerCkN8)
    }
    #[doc = "fSAMP=fDTS/2, N=6"]
    #[inline(always)]
    pub fn fdts_div2_n6(self) -> &'a mut crate::W<REG> {
        self.variant(Ch0capflt::FdtsDiv2N6)
    }
    #[doc = "fSAMP=fDTS/2, N=8"]
    #[inline(always)]
    pub fn fdts_div2_n8(self) -> &'a mut crate::W<REG> {
        self.variant(Ch0capflt::FdtsDiv2N8)
    }
    #[doc = "fSAMP=fDTS/4, N=6"]
    #[inline(always)]
    pub fn fdts_div4_n6(self) -> &'a mut crate::W<REG> {
        self.variant(Ch0capflt::FdtsDiv4N6)
    }
    #[doc = "fSAMP=fDTS/4, N=8"]
    #[inline(always)]
    pub fn fdts_div4_n8(self) -> &'a mut crate::W<REG> {
        self.variant(Ch0capflt::FdtsDiv4N8)
    }
    #[doc = "fSAMP=fDTS/8, N=6"]
    #[inline(always)]
    pub fn fdts_div8_n6(self) -> &'a mut crate::W<REG> {
        self.variant(Ch0capflt::FdtsDiv8N6)
    }
    #[doc = "fSAMP=fDTS/8, N=8"]
    #[inline(always)]
    pub fn fdts_div8_n8(self) -> &'a mut crate::W<REG> {
        self.variant(Ch0capflt::FdtsDiv8N8)
    }
    #[doc = "fSAMP=fDTS/16, N=5"]
    #[inline(always)]
    pub fn fdts_div16_n5(self) -> &'a mut crate::W<REG> {
        self.variant(Ch0capflt::FdtsDiv16N5)
    }
    #[doc = "fSAMP=fDTS/16, N=6"]
    #[inline(always)]
    pub fn fdts_div16_n6(self) -> &'a mut crate::W<REG> {
        self.variant(Ch0capflt::FdtsDiv16N6)
    }
    #[doc = "fSAMP=fDTS/16, N=8"]
    #[inline(always)]
    pub fn fdts_div16_n8(self) -> &'a mut crate::W<REG> {
        self.variant(Ch0capflt::FdtsDiv16N8)
    }
    #[doc = "fSAMP=fDTS/32, N=5"]
    #[inline(always)]
    pub fn fdts_div32_n5(self) -> &'a mut crate::W<REG> {
        self.variant(Ch0capflt::FdtsDiv32N5)
    }
    #[doc = "fSAMP=fDTS/32, N=6"]
    #[inline(always)]
    pub fn fdts_div32_n6(self) -> &'a mut crate::W<REG> {
        self.variant(Ch0capflt::FdtsDiv32N6)
    }
    #[doc = "fSAMP=fDTS/32, N=8"]
    #[inline(always)]
    pub fn fdts_div32_n8(self) -> &'a mut crate::W<REG> {
        self.variant(Ch0capflt::FdtsDiv32N8)
    }
}
#[doc = "Field `CH1CAPFLT` reader - Channel 1 input capture filter control"]
pub use Ch0capfltR as Ch1capfltR;
#[doc = "Field `CH1CAPFLT` writer - Channel 1 input capture filter control"]
pub use Ch0capfltW as Ch1capfltW;
#[doc = "Field `CH1CAPPSC` reader - Channel 1 input capture prescaler"]
pub use Ch0cappscR as Ch1cappscR;
#[doc = "Field `CH1CAPPSC` writer - Channel 1 input capture prescaler"]
pub use Ch0cappscW as Ch1cappscW;
#[doc = "Field `CH1MS` reader - Channel 1 mode selection"]
pub use Ch0msR as Ch1msR;
#[doc = "Field `CH1MS` writer - Channel 1 mode selection"]
pub use Ch0msW as Ch1msW;
impl R {
    #[doc = "Bits 0:1 - Channel 0 mode selection"]
    #[inline(always)]
    pub fn ch0ms(&self) -> Ch0msR {
        Ch0msR::new((self.bits & 3) as u8)
    }
    #[doc = "Bits 2:3 - Channel 0 input capture prescaler"]
    #[inline(always)]
    pub fn ch0cappsc(&self) -> Ch0cappscR {
        Ch0cappscR::new(((self.bits >> 2) & 3) as u8)
    }
    #[doc = "Bits 4:7 - Channel 0 input capture filter control"]
    #[inline(always)]
    pub fn ch0capflt(&self) -> Ch0capfltR {
        Ch0capfltR::new(((self.bits >> 4) & 0x0f) as u8)
    }
    #[doc = "Bits 8:9 - Channel 1 mode selection"]
    #[inline(always)]
    pub fn ch1ms(&self) -> Ch1msR {
        Ch1msR::new(((self.bits >> 8) & 3) as u8)
    }
    #[doc = "Bits 10:11 - Channel 1 input capture prescaler"]
    #[inline(always)]
    pub fn ch1cappsc(&self) -> Ch1cappscR {
        Ch1cappscR::new(((self.bits >> 10) & 3) as u8)
    }
    #[doc = "Bits 12:15 - Channel 1 input capture filter control"]
    #[inline(always)]
    pub fn ch1capflt(&self) -> Ch1capfltR {
        Ch1capfltR::new(((self.bits >> 12) & 0x0f) as u8)
    }
}
impl W {
    #[doc = "Bits 0:1 - Channel 0 mode selection"]
    #[inline(always)]
    #[must_use]
    pub fn ch0ms(&mut self) -> Ch0msW<Chctl0InputSpec> {
        Ch0msW::new(self, 0)
    }
    #[doc = "Bits 2:3 - Channel 0 input capture prescaler"]
    #[inline(always)]
    #[must_use]
    pub fn ch0cappsc(&mut self) -> Ch0cappscW<Chctl0InputSpec> {
        Ch0cappscW::new(self, 2)
    }
    #[doc = "Bits 4:7 - Channel 0 input capture filter control"]
    #[inline(always)]
    #[must_use]
    pub fn ch0capflt(&mut self) -> Ch0capfltW<Chctl0InputSpec> {
        Ch0capfltW::new(self, 4)
    }
    #[doc = "Bits 8:9 - Channel 1 mode selection"]
    #[inline(always)]
    #[must_use]
    pub fn ch1ms(&mut self) -> Ch1msW<Chctl0InputSpec> {
        Ch1msW::new(self, 8)
    }
    #[doc = "Bits 10:11 - Channel 1 input capture prescaler"]
    #[inline(always)]
    #[must_use]
    pub fn ch1cappsc(&mut self) -> Ch1cappscW<Chctl0InputSpec> {
        Ch1cappscW::new(self, 10)
    }
    #[doc = "Bits 12:15 - Channel 1 input capture filter control"]
    #[inline(always)]
    #[must_use]
    pub fn ch1capflt(&mut self) -> Ch1capfltW<Chctl0InputSpec> {
        Ch1capfltW::new(self, 12)
    }
}
#[doc = "Channel control register 0 (input mode)\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`chctl0_input::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`chctl0_input::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct Chctl0InputSpec;
impl crate::RegisterSpec for Chctl0InputSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`chctl0_input::R`](R) reader structure"]
impl crate::Readable for Chctl0InputSpec {}
#[doc = "`write(|w| ..)` method takes [`chctl0_input::W`](W) writer structure"]
impl crate::Writable for Chctl0InputSpec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets CHCTL0_Input to value 0"]
impl crate::Resettable for Chctl0InputSpec {
    const RESET_VALUE: u32 = 0;
}
