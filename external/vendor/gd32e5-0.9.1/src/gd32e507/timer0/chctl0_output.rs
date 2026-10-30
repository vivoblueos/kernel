#[doc = "Register `CHCTL0_Output` reader"]
pub type R = crate::R<Chctl0OutputSpec>;
#[doc = "Register `CHCTL0_Output` writer"]
pub type W = crate::W<Chctl0OutputSpec>;
#[doc = "Channel 0 I/O mode selection\n\nValue on reset: 0"]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u8)]
pub enum Ch0ms {
    #[doc = "0: Channel is configured as output"]
    Output = 0,
    #[doc = "1: Channel is configured as input, ISx is connected to CI0FE0"]
    Ci0 = 1,
    #[doc = "2: Channel is configured as input, ISx is connected to CI1FE0"]
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
#[doc = "Field `CH0MS` reader - Channel 0 I/O mode selection"]
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
    #[doc = "Channel is configured as input, ISx is connected to CI0FE0"]
    #[inline(always)]
    pub fn is_ci0(&self) -> bool {
        *self == Ch0ms::Ci0
    }
    #[doc = "Channel is configured as input, ISx is connected to CI1FE0"]
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
#[doc = "Field `CH0MS` writer - Channel 0 I/O mode selection"]
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
    #[doc = "Channel is configured as input, ISx is connected to CI0FE0"]
    #[inline(always)]
    pub fn ci0(self) -> &'a mut crate::W<REG> {
        self.variant(Ch0ms::Ci0)
    }
    #[doc = "Channel is configured as input, ISx is connected to CI1FE0"]
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
#[doc = "Channel 0 output compare fast enable\n\nValue on reset: 0"]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Ch0comfen {
    #[doc = "0: The minimum delay from an edge is 5 clock cycles"]
    Slow = 0,
    #[doc = "1: The minimum delay from an edge is 3 clock cycles"]
    Fast = 1,
}
impl From<Ch0comfen> for bool {
    #[inline(always)]
    fn from(variant: Ch0comfen) -> Self {
        variant as u8 != 0
    }
}
#[doc = "Field `CH0COMFEN` reader - Channel 0 output compare fast enable"]
pub type Ch0comfenR = crate::BitReader<Ch0comfen>;
impl Ch0comfenR {
    #[doc = "Get enumerated values variant"]
    #[inline(always)]
    pub const fn variant(&self) -> Ch0comfen {
        match self.bits {
            false => Ch0comfen::Slow,
            true => Ch0comfen::Fast,
        }
    }
    #[doc = "The minimum delay from an edge is 5 clock cycles"]
    #[inline(always)]
    pub fn is_slow(&self) -> bool {
        *self == Ch0comfen::Slow
    }
    #[doc = "The minimum delay from an edge is 3 clock cycles"]
    #[inline(always)]
    pub fn is_fast(&self) -> bool {
        *self == Ch0comfen::Fast
    }
}
#[doc = "Field `CH0COMFEN` writer - Channel 0 output compare fast enable"]
pub type Ch0comfenW<'a, REG> = crate::BitWriter<'a, REG, Ch0comfen>;
impl<'a, REG> Ch0comfenW<'a, REG>
where
    REG: crate::Writable + crate::RegisterSpec,
{
    #[doc = "The minimum delay from an edge is 5 clock cycles"]
    #[inline(always)]
    pub fn slow(self) -> &'a mut crate::W<REG> {
        self.variant(Ch0comfen::Slow)
    }
    #[doc = "The minimum delay from an edge is 3 clock cycles"]
    #[inline(always)]
    pub fn fast(self) -> &'a mut crate::W<REG> {
        self.variant(Ch0comfen::Fast)
    }
}
#[doc = "Channel 0 compare output shadow enable\n\nValue on reset: 0"]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Ch0comsen {
    #[doc = "0: Preload register on CHyCV disabled. New values written to CHyCV are taken into account immediately"]
    Disabled = 0,
    #[doc = "1: Preload register on CHyCV enabled. Preload value is loaded into active register on each update event"]
    Enabled = 1,
}
impl From<Ch0comsen> for bool {
    #[inline(always)]
    fn from(variant: Ch0comsen) -> Self {
        variant as u8 != 0
    }
}
#[doc = "Field `CH0COMSEN` reader - Channel 0 compare output shadow enable"]
pub type Ch0comsenR = crate::BitReader<Ch0comsen>;
impl Ch0comsenR {
    #[doc = "Get enumerated values variant"]
    #[inline(always)]
    pub const fn variant(&self) -> Ch0comsen {
        match self.bits {
            false => Ch0comsen::Disabled,
            true => Ch0comsen::Enabled,
        }
    }
    #[doc = "Preload register on CHyCV disabled. New values written to CHyCV are taken into account immediately"]
    #[inline(always)]
    pub fn is_disabled(&self) -> bool {
        *self == Ch0comsen::Disabled
    }
    #[doc = "Preload register on CHyCV enabled. Preload value is loaded into active register on each update event"]
    #[inline(always)]
    pub fn is_enabled(&self) -> bool {
        *self == Ch0comsen::Enabled
    }
}
#[doc = "Field `CH0COMSEN` writer - Channel 0 compare output shadow enable"]
pub type Ch0comsenW<'a, REG> = crate::BitWriter<'a, REG, Ch0comsen>;
impl<'a, REG> Ch0comsenW<'a, REG>
where
    REG: crate::Writable + crate::RegisterSpec,
{
    #[doc = "Preload register on CHyCV disabled. New values written to CHyCV are taken into account immediately"]
    #[inline(always)]
    pub fn disabled(self) -> &'a mut crate::W<REG> {
        self.variant(Ch0comsen::Disabled)
    }
    #[doc = "Preload register on CHyCV enabled. Preload value is loaded into active register on each update event"]
    #[inline(always)]
    pub fn enabled(self) -> &'a mut crate::W<REG> {
        self.variant(Ch0comsen::Enabled)
    }
}
#[doc = "Channel 0 compare output control\n\nValue on reset: 0"]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u8)]
pub enum Ch0comctl {
    #[doc = "0: The comparison between the output compare register CHyCV and the counter CNT has no effect on the outputs"]
    Frozen = 0,
    #[doc = "1: Set channel to active level on match. OxCPRE signal is forced high when the counter matches the capture/compare register CHyCV"]
    ActiveOnMatch = 1,
    #[doc = "2: Set channel to inactive level on match. OxCPRE signal is forced low when the counter matches the capture/compare register CHyCV"]
    InactiveOnMatch = 2,
    #[doc = "3: OxCPRE toggles when CNT=CHyCV"]
    Toggle = 3,
    #[doc = "4: OxCPRE is forced low"]
    ForceInactive = 4,
    #[doc = "5: OxCPRE is forced high"]
    ForceActive = 5,
    #[doc = "6: In upcounting, channel is active as long as CNT&lt;CHyCV else inactive. In downcounting, channel is inactive as long as CNT>CHyCV else active"]
    PwmMode0 = 6,
    #[doc = "7: Inversely to PwmMode0"]
    PwmMode1 = 7,
}
impl From<Ch0comctl> for u8 {
    #[inline(always)]
    fn from(variant: Ch0comctl) -> Self {
        variant as _
    }
}
impl crate::FieldSpec for Ch0comctl {
    type Ux = u8;
}
#[doc = "Field `CH0COMCTL` reader - Channel 0 compare output control"]
pub type Ch0comctlR = crate::FieldReader<Ch0comctl>;
impl Ch0comctlR {
    #[doc = "Get enumerated values variant"]
    #[inline(always)]
    pub const fn variant(&self) -> Ch0comctl {
        match self.bits {
            0 => Ch0comctl::Frozen,
            1 => Ch0comctl::ActiveOnMatch,
            2 => Ch0comctl::InactiveOnMatch,
            3 => Ch0comctl::Toggle,
            4 => Ch0comctl::ForceInactive,
            5 => Ch0comctl::ForceActive,
            6 => Ch0comctl::PwmMode0,
            7 => Ch0comctl::PwmMode1,
            _ => unreachable!(),
        }
    }
    #[doc = "The comparison between the output compare register CHyCV and the counter CNT has no effect on the outputs"]
    #[inline(always)]
    pub fn is_frozen(&self) -> bool {
        *self == Ch0comctl::Frozen
    }
    #[doc = "Set channel to active level on match. OxCPRE signal is forced high when the counter matches the capture/compare register CHyCV"]
    #[inline(always)]
    pub fn is_active_on_match(&self) -> bool {
        *self == Ch0comctl::ActiveOnMatch
    }
    #[doc = "Set channel to inactive level on match. OxCPRE signal is forced low when the counter matches the capture/compare register CHyCV"]
    #[inline(always)]
    pub fn is_inactive_on_match(&self) -> bool {
        *self == Ch0comctl::InactiveOnMatch
    }
    #[doc = "OxCPRE toggles when CNT=CHyCV"]
    #[inline(always)]
    pub fn is_toggle(&self) -> bool {
        *self == Ch0comctl::Toggle
    }
    #[doc = "OxCPRE is forced low"]
    #[inline(always)]
    pub fn is_force_inactive(&self) -> bool {
        *self == Ch0comctl::ForceInactive
    }
    #[doc = "OxCPRE is forced high"]
    #[inline(always)]
    pub fn is_force_active(&self) -> bool {
        *self == Ch0comctl::ForceActive
    }
    #[doc = "In upcounting, channel is active as long as CNT&lt;CHyCV else inactive. In downcounting, channel is inactive as long as CNT>CHyCV else active"]
    #[inline(always)]
    pub fn is_pwm_mode0(&self) -> bool {
        *self == Ch0comctl::PwmMode0
    }
    #[doc = "Inversely to PwmMode0"]
    #[inline(always)]
    pub fn is_pwm_mode1(&self) -> bool {
        *self == Ch0comctl::PwmMode1
    }
}
#[doc = "Field `CH0COMCTL` writer - Channel 0 compare output control"]
pub type Ch0comctlW<'a, REG> = crate::FieldWriterSafe<'a, REG, 3, Ch0comctl>;
impl<'a, REG> Ch0comctlW<'a, REG>
where
    REG: crate::Writable + crate::RegisterSpec,
    REG::Ux: From<u8>,
{
    #[doc = "The comparison between the output compare register CHyCV and the counter CNT has no effect on the outputs"]
    #[inline(always)]
    pub fn frozen(self) -> &'a mut crate::W<REG> {
        self.variant(Ch0comctl::Frozen)
    }
    #[doc = "Set channel to active level on match. OxCPRE signal is forced high when the counter matches the capture/compare register CHyCV"]
    #[inline(always)]
    pub fn active_on_match(self) -> &'a mut crate::W<REG> {
        self.variant(Ch0comctl::ActiveOnMatch)
    }
    #[doc = "Set channel to inactive level on match. OxCPRE signal is forced low when the counter matches the capture/compare register CHyCV"]
    #[inline(always)]
    pub fn inactive_on_match(self) -> &'a mut crate::W<REG> {
        self.variant(Ch0comctl::InactiveOnMatch)
    }
    #[doc = "OxCPRE toggles when CNT=CHyCV"]
    #[inline(always)]
    pub fn toggle(self) -> &'a mut crate::W<REG> {
        self.variant(Ch0comctl::Toggle)
    }
    #[doc = "OxCPRE is forced low"]
    #[inline(always)]
    pub fn force_inactive(self) -> &'a mut crate::W<REG> {
        self.variant(Ch0comctl::ForceInactive)
    }
    #[doc = "OxCPRE is forced high"]
    #[inline(always)]
    pub fn force_active(self) -> &'a mut crate::W<REG> {
        self.variant(Ch0comctl::ForceActive)
    }
    #[doc = "In upcounting, channel is active as long as CNT&lt;CHyCV else inactive. In downcounting, channel is inactive as long as CNT>CHyCV else active"]
    #[inline(always)]
    pub fn pwm_mode0(self) -> &'a mut crate::W<REG> {
        self.variant(Ch0comctl::PwmMode0)
    }
    #[doc = "Inversely to PwmMode0"]
    #[inline(always)]
    pub fn pwm_mode1(self) -> &'a mut crate::W<REG> {
        self.variant(Ch0comctl::PwmMode1)
    }
}
#[doc = "Channel 0 output compare clear enable\n\nValue on reset: 0"]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Ch0comcen {
    #[doc = "0: Output compare clear disabled"]
    Disabled = 0,
    #[doc = "1: Output compare clear enabled"]
    Enabled = 1,
}
impl From<Ch0comcen> for bool {
    #[inline(always)]
    fn from(variant: Ch0comcen) -> Self {
        variant as u8 != 0
    }
}
#[doc = "Field `CH0COMCEN` reader - Channel 0 output compare clear enable"]
pub type Ch0comcenR = crate::BitReader<Ch0comcen>;
impl Ch0comcenR {
    #[doc = "Get enumerated values variant"]
    #[inline(always)]
    pub const fn variant(&self) -> Ch0comcen {
        match self.bits {
            false => Ch0comcen::Disabled,
            true => Ch0comcen::Enabled,
        }
    }
    #[doc = "Output compare clear disabled"]
    #[inline(always)]
    pub fn is_disabled(&self) -> bool {
        *self == Ch0comcen::Disabled
    }
    #[doc = "Output compare clear enabled"]
    #[inline(always)]
    pub fn is_enabled(&self) -> bool {
        *self == Ch0comcen::Enabled
    }
}
#[doc = "Field `CH0COMCEN` writer - Channel 0 output compare clear enable"]
pub type Ch0comcenW<'a, REG> = crate::BitWriter<'a, REG, Ch0comcen>;
impl<'a, REG> Ch0comcenW<'a, REG>
where
    REG: crate::Writable + crate::RegisterSpec,
{
    #[doc = "Output compare clear disabled"]
    #[inline(always)]
    pub fn disabled(self) -> &'a mut crate::W<REG> {
        self.variant(Ch0comcen::Disabled)
    }
    #[doc = "Output compare clear enabled"]
    #[inline(always)]
    pub fn enabled(self) -> &'a mut crate::W<REG> {
        self.variant(Ch0comcen::Enabled)
    }
}
#[doc = "Field `CH1COMCEN` reader - Channel 1 output compare clear enable"]
pub use Ch0comcenR as Ch1comcenR;
#[doc = "Field `CH1COMCEN` writer - Channel 1 output compare clear enable"]
pub use Ch0comcenW as Ch1comcenW;
#[doc = "Field `CH1COMCTL` reader - Channel 1 compare output control"]
pub use Ch0comctlR as Ch1comctlR;
#[doc = "Field `CH1COMCTL` writer - Channel 1 compare output control"]
pub use Ch0comctlW as Ch1comctlW;
#[doc = "Field `CH1COMFEN` reader - Channel 1 output compare fast enable"]
pub use Ch0comfenR as Ch1comfenR;
#[doc = "Field `CH1COMFEN` writer - Channel 1 output compare fast enable"]
pub use Ch0comfenW as Ch1comfenW;
#[doc = "Field `CH1COMSEN` reader - Channel 1 output compare shadow enable"]
pub use Ch0comsenR as Ch1comsenR;
#[doc = "Field `CH1COMSEN` writer - Channel 1 output compare shadow enable"]
pub use Ch0comsenW as Ch1comsenW;
#[doc = "Field `CH1MS` reader - Channel 1 mode selection"]
pub use Ch0msR as Ch1msR;
#[doc = "Field `CH1MS` writer - Channel 1 mode selection"]
pub use Ch0msW as Ch1msW;
impl R {
    #[doc = "Bits 0:1 - Channel 0 I/O mode selection"]
    #[inline(always)]
    pub fn ch0ms(&self) -> Ch0msR {
        Ch0msR::new((self.bits & 3) as u8)
    }
    #[doc = "Bit 2 - Channel 0 output compare fast enable"]
    #[inline(always)]
    pub fn ch0comfen(&self) -> Ch0comfenR {
        Ch0comfenR::new(((self.bits >> 2) & 1) != 0)
    }
    #[doc = "Bit 3 - Channel 0 compare output shadow enable"]
    #[inline(always)]
    pub fn ch0comsen(&self) -> Ch0comsenR {
        Ch0comsenR::new(((self.bits >> 3) & 1) != 0)
    }
    #[doc = "Bits 4:6 - Channel 0 compare output control"]
    #[inline(always)]
    pub fn ch0comctl(&self) -> Ch0comctlR {
        Ch0comctlR::new(((self.bits >> 4) & 7) as u8)
    }
    #[doc = "Bit 7 - Channel 0 output compare clear enable"]
    #[inline(always)]
    pub fn ch0comcen(&self) -> Ch0comcenR {
        Ch0comcenR::new(((self.bits >> 7) & 1) != 0)
    }
    #[doc = "Bits 8:9 - Channel 1 mode selection"]
    #[inline(always)]
    pub fn ch1ms(&self) -> Ch1msR {
        Ch1msR::new(((self.bits >> 8) & 3) as u8)
    }
    #[doc = "Bit 10 - Channel 1 output compare fast enable"]
    #[inline(always)]
    pub fn ch1comfen(&self) -> Ch1comfenR {
        Ch1comfenR::new(((self.bits >> 10) & 1) != 0)
    }
    #[doc = "Bit 11 - Channel 1 output compare shadow enable"]
    #[inline(always)]
    pub fn ch1comsen(&self) -> Ch1comsenR {
        Ch1comsenR::new(((self.bits >> 11) & 1) != 0)
    }
    #[doc = "Bits 12:14 - Channel 1 compare output control"]
    #[inline(always)]
    pub fn ch1comctl(&self) -> Ch1comctlR {
        Ch1comctlR::new(((self.bits >> 12) & 7) as u8)
    }
    #[doc = "Bit 15 - Channel 1 output compare clear enable"]
    #[inline(always)]
    pub fn ch1comcen(&self) -> Ch1comcenR {
        Ch1comcenR::new(((self.bits >> 15) & 1) != 0)
    }
}
impl W {
    #[doc = "Bits 0:1 - Channel 0 I/O mode selection"]
    #[inline(always)]
    #[must_use]
    pub fn ch0ms(&mut self) -> Ch0msW<Chctl0OutputSpec> {
        Ch0msW::new(self, 0)
    }
    #[doc = "Bit 2 - Channel 0 output compare fast enable"]
    #[inline(always)]
    #[must_use]
    pub fn ch0comfen(&mut self) -> Ch0comfenW<Chctl0OutputSpec> {
        Ch0comfenW::new(self, 2)
    }
    #[doc = "Bit 3 - Channel 0 compare output shadow enable"]
    #[inline(always)]
    #[must_use]
    pub fn ch0comsen(&mut self) -> Ch0comsenW<Chctl0OutputSpec> {
        Ch0comsenW::new(self, 3)
    }
    #[doc = "Bits 4:6 - Channel 0 compare output control"]
    #[inline(always)]
    #[must_use]
    pub fn ch0comctl(&mut self) -> Ch0comctlW<Chctl0OutputSpec> {
        Ch0comctlW::new(self, 4)
    }
    #[doc = "Bit 7 - Channel 0 output compare clear enable"]
    #[inline(always)]
    #[must_use]
    pub fn ch0comcen(&mut self) -> Ch0comcenW<Chctl0OutputSpec> {
        Ch0comcenW::new(self, 7)
    }
    #[doc = "Bits 8:9 - Channel 1 mode selection"]
    #[inline(always)]
    #[must_use]
    pub fn ch1ms(&mut self) -> Ch1msW<Chctl0OutputSpec> {
        Ch1msW::new(self, 8)
    }
    #[doc = "Bit 10 - Channel 1 output compare fast enable"]
    #[inline(always)]
    #[must_use]
    pub fn ch1comfen(&mut self) -> Ch1comfenW<Chctl0OutputSpec> {
        Ch1comfenW::new(self, 10)
    }
    #[doc = "Bit 11 - Channel 1 output compare shadow enable"]
    #[inline(always)]
    #[must_use]
    pub fn ch1comsen(&mut self) -> Ch1comsenW<Chctl0OutputSpec> {
        Ch1comsenW::new(self, 11)
    }
    #[doc = "Bits 12:14 - Channel 1 compare output control"]
    #[inline(always)]
    #[must_use]
    pub fn ch1comctl(&mut self) -> Ch1comctlW<Chctl0OutputSpec> {
        Ch1comctlW::new(self, 12)
    }
    #[doc = "Bit 15 - Channel 1 output compare clear enable"]
    #[inline(always)]
    #[must_use]
    pub fn ch1comcen(&mut self) -> Ch1comcenW<Chctl0OutputSpec> {
        Ch1comcenW::new(self, 15)
    }
}
#[doc = "Channel control register 0 (output mode)\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`chctl0_output::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`chctl0_output::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct Chctl0OutputSpec;
impl crate::RegisterSpec for Chctl0OutputSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`chctl0_output::R`](R) reader structure"]
impl crate::Readable for Chctl0OutputSpec {}
#[doc = "`write(|w| ..)` method takes [`chctl0_output::W`](W) writer structure"]
impl crate::Writable for Chctl0OutputSpec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets CHCTL0_Output to value 0"]
impl crate::Resettable for Chctl0OutputSpec {
    const RESET_VALUE: u32 = 0;
}
