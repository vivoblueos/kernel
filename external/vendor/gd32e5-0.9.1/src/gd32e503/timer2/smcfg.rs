#[doc = "Register `SMCFG` reader"]
pub type R = crate::R<SmcfgSpec>;
#[doc = "Register `SMCFG` writer"]
pub type W = crate::W<SmcfgSpec>;
#[doc = "Slave mode control\n\nValue on reset: 0"]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u8)]
pub enum Smc {
    #[doc = "0: Slave mode disabled - if CEN=1 then the prescaler is clocked directly by the internal clock."]
    Disabled = 0,
    #[doc = "1: Quadrature decoder mode 0 - Counter counts up/down on CI1FE1 edge depending on CI0FE0 level."]
    QuadratureDecoderMode0 = 1,
    #[doc = "2: Quadrature decoder mode 1 - Counter counts up/down on CI0FE0 edge depending on CI1FE1 level."]
    QuadratureDecoderMode1 = 2,
    #[doc = "3: Quadrature decoder mode 2 - Counter counts up/down on both CI0FE0 and CI1FE1 edges depending on the level of the other input."]
    QuadratureDecoderMode2 = 3,
    #[doc = "4: Restart Mode - Rising edge of the selected trigger input (TRGI) reinitializes the counter and generates an update of the registers."]
    RestartMode = 4,
    #[doc = "5: Pause Mode - The counter clock is enabled when the trigger input (TRGI) is high. The counter stops (but is not reset) as soon as the trigger becomes low. Both start and stop of the counter are controlled."]
    PauseMode = 5,
    #[doc = "6: Event Mode - The counter starts at a rising edge of the trigger TRGI (but it is not reset). Only the start of the counter is controlled."]
    EventMode = 6,
    #[doc = "7: External Clock Mode 0 - Rising edges of the selected trigger (TRGI) clock the counter."]
    ExternalClockMode = 7,
}
impl From<Smc> for u8 {
    #[inline(always)]
    fn from(variant: Smc) -> Self {
        variant as _
    }
}
impl crate::FieldSpec for Smc {
    type Ux = u8;
}
#[doc = "Field `SMC` reader - Slave mode control"]
pub type SmcR = crate::FieldReader<Smc>;
impl SmcR {
    #[doc = "Get enumerated values variant"]
    #[inline(always)]
    pub const fn variant(&self) -> Smc {
        match self.bits {
            0 => Smc::Disabled,
            1 => Smc::QuadratureDecoderMode0,
            2 => Smc::QuadratureDecoderMode1,
            3 => Smc::QuadratureDecoderMode2,
            4 => Smc::RestartMode,
            5 => Smc::PauseMode,
            6 => Smc::EventMode,
            7 => Smc::ExternalClockMode,
            _ => unreachable!(),
        }
    }
    #[doc = "Slave mode disabled - if CEN=1 then the prescaler is clocked directly by the internal clock."]
    #[inline(always)]
    pub fn is_disabled(&self) -> bool {
        *self == Smc::Disabled
    }
    #[doc = "Quadrature decoder mode 0 - Counter counts up/down on CI1FE1 edge depending on CI0FE0 level."]
    #[inline(always)]
    pub fn is_quadrature_decoder_mode0(&self) -> bool {
        *self == Smc::QuadratureDecoderMode0
    }
    #[doc = "Quadrature decoder mode 1 - Counter counts up/down on CI0FE0 edge depending on CI1FE1 level."]
    #[inline(always)]
    pub fn is_quadrature_decoder_mode1(&self) -> bool {
        *self == Smc::QuadratureDecoderMode1
    }
    #[doc = "Quadrature decoder mode 2 - Counter counts up/down on both CI0FE0 and CI1FE1 edges depending on the level of the other input."]
    #[inline(always)]
    pub fn is_quadrature_decoder_mode2(&self) -> bool {
        *self == Smc::QuadratureDecoderMode2
    }
    #[doc = "Restart Mode - Rising edge of the selected trigger input (TRGI) reinitializes the counter and generates an update of the registers."]
    #[inline(always)]
    pub fn is_restart_mode(&self) -> bool {
        *self == Smc::RestartMode
    }
    #[doc = "Pause Mode - The counter clock is enabled when the trigger input (TRGI) is high. The counter stops (but is not reset) as soon as the trigger becomes low. Both start and stop of the counter are controlled."]
    #[inline(always)]
    pub fn is_pause_mode(&self) -> bool {
        *self == Smc::PauseMode
    }
    #[doc = "Event Mode - The counter starts at a rising edge of the trigger TRGI (but it is not reset). Only the start of the counter is controlled."]
    #[inline(always)]
    pub fn is_event_mode(&self) -> bool {
        *self == Smc::EventMode
    }
    #[doc = "External Clock Mode 0 - Rising edges of the selected trigger (TRGI) clock the counter."]
    #[inline(always)]
    pub fn is_external_clock_mode(&self) -> bool {
        *self == Smc::ExternalClockMode
    }
}
#[doc = "Field `SMC` writer - Slave mode control"]
pub type SmcW<'a, REG> = crate::FieldWriterSafe<'a, REG, 3, Smc>;
impl<'a, REG> SmcW<'a, REG>
where
    REG: crate::Writable + crate::RegisterSpec,
    REG::Ux: From<u8>,
{
    #[doc = "Slave mode disabled - if CEN=1 then the prescaler is clocked directly by the internal clock."]
    #[inline(always)]
    pub fn disabled(self) -> &'a mut crate::W<REG> {
        self.variant(Smc::Disabled)
    }
    #[doc = "Quadrature decoder mode 0 - Counter counts up/down on CI1FE1 edge depending on CI0FE0 level."]
    #[inline(always)]
    pub fn quadrature_decoder_mode0(self) -> &'a mut crate::W<REG> {
        self.variant(Smc::QuadratureDecoderMode0)
    }
    #[doc = "Quadrature decoder mode 1 - Counter counts up/down on CI0FE0 edge depending on CI1FE1 level."]
    #[inline(always)]
    pub fn quadrature_decoder_mode1(self) -> &'a mut crate::W<REG> {
        self.variant(Smc::QuadratureDecoderMode1)
    }
    #[doc = "Quadrature decoder mode 2 - Counter counts up/down on both CI0FE0 and CI1FE1 edges depending on the level of the other input."]
    #[inline(always)]
    pub fn quadrature_decoder_mode2(self) -> &'a mut crate::W<REG> {
        self.variant(Smc::QuadratureDecoderMode2)
    }
    #[doc = "Restart Mode - Rising edge of the selected trigger input (TRGI) reinitializes the counter and generates an update of the registers."]
    #[inline(always)]
    pub fn restart_mode(self) -> &'a mut crate::W<REG> {
        self.variant(Smc::RestartMode)
    }
    #[doc = "Pause Mode - The counter clock is enabled when the trigger input (TRGI) is high. The counter stops (but is not reset) as soon as the trigger becomes low. Both start and stop of the counter are controlled."]
    #[inline(always)]
    pub fn pause_mode(self) -> &'a mut crate::W<REG> {
        self.variant(Smc::PauseMode)
    }
    #[doc = "Event Mode - The counter starts at a rising edge of the trigger TRGI (but it is not reset). Only the start of the counter is controlled."]
    #[inline(always)]
    pub fn event_mode(self) -> &'a mut crate::W<REG> {
        self.variant(Smc::EventMode)
    }
    #[doc = "External Clock Mode 0 - Rising edges of the selected trigger (TRGI) clock the counter."]
    #[inline(always)]
    pub fn external_clock_mode(self) -> &'a mut crate::W<REG> {
        self.variant(Smc::ExternalClockMode)
    }
}
#[doc = "Trigger selection\n\nValue on reset: 0"]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u8)]
pub enum Trgs {
    #[doc = "0: Internal Trigger 0 (ITI0)"]
    Iti0 = 0,
    #[doc = "1: Internal Trigger 1 (ITI1)"]
    Iti1 = 1,
    #[doc = "2: Internal Trigger 2 (ITI2)"]
    Iti2 = 2,
    #[doc = "4: CI0 Edge Detector (CI0F_ED)"]
    Ci0fEd = 4,
    #[doc = "5: Filtered Timer Input 0 (CI0FE0)"]
    Ci0fe0 = 5,
    #[doc = "6: Filtered Timer Input 1 (CI1FE1)"]
    Ci1fe1 = 6,
    #[doc = "7: External Trigger input (ETIFP)"]
    Etifp = 7,
}
impl From<Trgs> for u8 {
    #[inline(always)]
    fn from(variant: Trgs) -> Self {
        variant as _
    }
}
impl crate::FieldSpec for Trgs {
    type Ux = u8;
}
#[doc = "Field `TRGS` reader - Trigger selection"]
pub type TrgsR = crate::FieldReader<Trgs>;
impl TrgsR {
    #[doc = "Get enumerated values variant"]
    #[inline(always)]
    pub const fn variant(&self) -> Option<Trgs> {
        match self.bits {
            0 => Some(Trgs::Iti0),
            1 => Some(Trgs::Iti1),
            2 => Some(Trgs::Iti2),
            4 => Some(Trgs::Ci0fEd),
            5 => Some(Trgs::Ci0fe0),
            6 => Some(Trgs::Ci1fe1),
            7 => Some(Trgs::Etifp),
            _ => None,
        }
    }
    #[doc = "Internal Trigger 0 (ITI0)"]
    #[inline(always)]
    pub fn is_iti0(&self) -> bool {
        *self == Trgs::Iti0
    }
    #[doc = "Internal Trigger 1 (ITI1)"]
    #[inline(always)]
    pub fn is_iti1(&self) -> bool {
        *self == Trgs::Iti1
    }
    #[doc = "Internal Trigger 2 (ITI2)"]
    #[inline(always)]
    pub fn is_iti2(&self) -> bool {
        *self == Trgs::Iti2
    }
    #[doc = "CI0 Edge Detector (CI0F_ED)"]
    #[inline(always)]
    pub fn is_ci0f_ed(&self) -> bool {
        *self == Trgs::Ci0fEd
    }
    #[doc = "Filtered Timer Input 0 (CI0FE0)"]
    #[inline(always)]
    pub fn is_ci0fe0(&self) -> bool {
        *self == Trgs::Ci0fe0
    }
    #[doc = "Filtered Timer Input 1 (CI1FE1)"]
    #[inline(always)]
    pub fn is_ci1fe1(&self) -> bool {
        *self == Trgs::Ci1fe1
    }
    #[doc = "External Trigger input (ETIFP)"]
    #[inline(always)]
    pub fn is_etifp(&self) -> bool {
        *self == Trgs::Etifp
    }
}
#[doc = "Field `TRGS` writer - Trigger selection"]
pub type TrgsW<'a, REG> = crate::FieldWriter<'a, REG, 3, Trgs>;
impl<'a, REG> TrgsW<'a, REG>
where
    REG: crate::Writable + crate::RegisterSpec,
    REG::Ux: From<u8>,
{
    #[doc = "Internal Trigger 0 (ITI0)"]
    #[inline(always)]
    pub fn iti0(self) -> &'a mut crate::W<REG> {
        self.variant(Trgs::Iti0)
    }
    #[doc = "Internal Trigger 1 (ITI1)"]
    #[inline(always)]
    pub fn iti1(self) -> &'a mut crate::W<REG> {
        self.variant(Trgs::Iti1)
    }
    #[doc = "Internal Trigger 2 (ITI2)"]
    #[inline(always)]
    pub fn iti2(self) -> &'a mut crate::W<REG> {
        self.variant(Trgs::Iti2)
    }
    #[doc = "CI0 Edge Detector (CI0F_ED)"]
    #[inline(always)]
    pub fn ci0f_ed(self) -> &'a mut crate::W<REG> {
        self.variant(Trgs::Ci0fEd)
    }
    #[doc = "Filtered Timer Input 0 (CI0FE0)"]
    #[inline(always)]
    pub fn ci0fe0(self) -> &'a mut crate::W<REG> {
        self.variant(Trgs::Ci0fe0)
    }
    #[doc = "Filtered Timer Input 1 (CI1FE1)"]
    #[inline(always)]
    pub fn ci1fe1(self) -> &'a mut crate::W<REG> {
        self.variant(Trgs::Ci1fe1)
    }
    #[doc = "External Trigger input (ETIFP)"]
    #[inline(always)]
    pub fn etifp(self) -> &'a mut crate::W<REG> {
        self.variant(Trgs::Etifp)
    }
}
#[doc = "Master-slave mode\n\nValue on reset: 0"]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Msm {
    #[doc = "0: No action"]
    NoSync = 0,
    #[doc = "1: The effect of an event on the trigger input (TRGI) is delayed to allow a perfect synchronization between the current timer and its slaves (through TRGO). It is useful if we want to synchronize several timers on a single external event."]
    Sync = 1,
}
impl From<Msm> for bool {
    #[inline(always)]
    fn from(variant: Msm) -> Self {
        variant as u8 != 0
    }
}
#[doc = "Field `MSM` reader - Master-slave mode"]
pub type MsmR = crate::BitReader<Msm>;
impl MsmR {
    #[doc = "Get enumerated values variant"]
    #[inline(always)]
    pub const fn variant(&self) -> Msm {
        match self.bits {
            false => Msm::NoSync,
            true => Msm::Sync,
        }
    }
    #[doc = "No action"]
    #[inline(always)]
    pub fn is_no_sync(&self) -> bool {
        *self == Msm::NoSync
    }
    #[doc = "The effect of an event on the trigger input (TRGI) is delayed to allow a perfect synchronization between the current timer and its slaves (through TRGO). It is useful if we want to synchronize several timers on a single external event."]
    #[inline(always)]
    pub fn is_sync(&self) -> bool {
        *self == Msm::Sync
    }
}
#[doc = "Field `MSM` writer - Master-slave mode"]
pub type MsmW<'a, REG> = crate::BitWriter<'a, REG, Msm>;
impl<'a, REG> MsmW<'a, REG>
where
    REG: crate::Writable + crate::RegisterSpec,
{
    #[doc = "No action"]
    #[inline(always)]
    pub fn no_sync(self) -> &'a mut crate::W<REG> {
        self.variant(Msm::NoSync)
    }
    #[doc = "The effect of an event on the trigger input (TRGI) is delayed to allow a perfect synchronization between the current timer and its slaves (through TRGO). It is useful if we want to synchronize several timers on a single external event."]
    #[inline(always)]
    pub fn sync(self) -> &'a mut crate::W<REG> {
        self.variant(Msm::Sync)
    }
}
#[doc = "External trigger filter control\n\nValue on reset: 0"]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u8)]
pub enum Etfc {
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
impl From<Etfc> for u8 {
    #[inline(always)]
    fn from(variant: Etfc) -> Self {
        variant as _
    }
}
impl crate::FieldSpec for Etfc {
    type Ux = u8;
}
#[doc = "Field `ETFC` reader - External trigger filter control"]
pub type EtfcR = crate::FieldReader<Etfc>;
impl EtfcR {
    #[doc = "Get enumerated values variant"]
    #[inline(always)]
    pub const fn variant(&self) -> Etfc {
        match self.bits {
            0 => Etfc::NoFilter,
            1 => Etfc::TimerCkN2,
            2 => Etfc::TimerCkN4,
            3 => Etfc::TimerCkN8,
            4 => Etfc::FdtsDiv2N6,
            5 => Etfc::FdtsDiv2N8,
            6 => Etfc::FdtsDiv4N6,
            7 => Etfc::FdtsDiv4N8,
            8 => Etfc::FdtsDiv8N6,
            9 => Etfc::FdtsDiv8N8,
            10 => Etfc::FdtsDiv16N5,
            11 => Etfc::FdtsDiv16N6,
            12 => Etfc::FdtsDiv16N8,
            13 => Etfc::FdtsDiv32N5,
            14 => Etfc::FdtsDiv32N6,
            15 => Etfc::FdtsDiv32N8,
            _ => unreachable!(),
        }
    }
    #[doc = "Filter disabled. fSAMP=fDTS, N=1"]
    #[inline(always)]
    pub fn is_no_filter(&self) -> bool {
        *self == Etfc::NoFilter
    }
    #[doc = "fSAMP=fTIMER_CK, N=2"]
    #[inline(always)]
    pub fn is_timer_ck_n2(&self) -> bool {
        *self == Etfc::TimerCkN2
    }
    #[doc = "fSAMP=fTIMER_CK, N=4"]
    #[inline(always)]
    pub fn is_timer_ck_n4(&self) -> bool {
        *self == Etfc::TimerCkN4
    }
    #[doc = "fSAMP=fTIMER_CK, N=8"]
    #[inline(always)]
    pub fn is_timer_ck_n8(&self) -> bool {
        *self == Etfc::TimerCkN8
    }
    #[doc = "fSAMP=fDTS/2, N=6"]
    #[inline(always)]
    pub fn is_fdts_div2_n6(&self) -> bool {
        *self == Etfc::FdtsDiv2N6
    }
    #[doc = "fSAMP=fDTS/2, N=8"]
    #[inline(always)]
    pub fn is_fdts_div2_n8(&self) -> bool {
        *self == Etfc::FdtsDiv2N8
    }
    #[doc = "fSAMP=fDTS/4, N=6"]
    #[inline(always)]
    pub fn is_fdts_div4_n6(&self) -> bool {
        *self == Etfc::FdtsDiv4N6
    }
    #[doc = "fSAMP=fDTS/4, N=8"]
    #[inline(always)]
    pub fn is_fdts_div4_n8(&self) -> bool {
        *self == Etfc::FdtsDiv4N8
    }
    #[doc = "fSAMP=fDTS/8, N=6"]
    #[inline(always)]
    pub fn is_fdts_div8_n6(&self) -> bool {
        *self == Etfc::FdtsDiv8N6
    }
    #[doc = "fSAMP=fDTS/8, N=8"]
    #[inline(always)]
    pub fn is_fdts_div8_n8(&self) -> bool {
        *self == Etfc::FdtsDiv8N8
    }
    #[doc = "fSAMP=fDTS/16, N=5"]
    #[inline(always)]
    pub fn is_fdts_div16_n5(&self) -> bool {
        *self == Etfc::FdtsDiv16N5
    }
    #[doc = "fSAMP=fDTS/16, N=6"]
    #[inline(always)]
    pub fn is_fdts_div16_n6(&self) -> bool {
        *self == Etfc::FdtsDiv16N6
    }
    #[doc = "fSAMP=fDTS/16, N=8"]
    #[inline(always)]
    pub fn is_fdts_div16_n8(&self) -> bool {
        *self == Etfc::FdtsDiv16N8
    }
    #[doc = "fSAMP=fDTS/32, N=5"]
    #[inline(always)]
    pub fn is_fdts_div32_n5(&self) -> bool {
        *self == Etfc::FdtsDiv32N5
    }
    #[doc = "fSAMP=fDTS/32, N=6"]
    #[inline(always)]
    pub fn is_fdts_div32_n6(&self) -> bool {
        *self == Etfc::FdtsDiv32N6
    }
    #[doc = "fSAMP=fDTS/32, N=8"]
    #[inline(always)]
    pub fn is_fdts_div32_n8(&self) -> bool {
        *self == Etfc::FdtsDiv32N8
    }
}
#[doc = "Field `ETFC` writer - External trigger filter control"]
pub type EtfcW<'a, REG> = crate::FieldWriterSafe<'a, REG, 4, Etfc>;
impl<'a, REG> EtfcW<'a, REG>
where
    REG: crate::Writable + crate::RegisterSpec,
    REG::Ux: From<u8>,
{
    #[doc = "Filter disabled. fSAMP=fDTS, N=1"]
    #[inline(always)]
    pub fn no_filter(self) -> &'a mut crate::W<REG> {
        self.variant(Etfc::NoFilter)
    }
    #[doc = "fSAMP=fTIMER_CK, N=2"]
    #[inline(always)]
    pub fn timer_ck_n2(self) -> &'a mut crate::W<REG> {
        self.variant(Etfc::TimerCkN2)
    }
    #[doc = "fSAMP=fTIMER_CK, N=4"]
    #[inline(always)]
    pub fn timer_ck_n4(self) -> &'a mut crate::W<REG> {
        self.variant(Etfc::TimerCkN4)
    }
    #[doc = "fSAMP=fTIMER_CK, N=8"]
    #[inline(always)]
    pub fn timer_ck_n8(self) -> &'a mut crate::W<REG> {
        self.variant(Etfc::TimerCkN8)
    }
    #[doc = "fSAMP=fDTS/2, N=6"]
    #[inline(always)]
    pub fn fdts_div2_n6(self) -> &'a mut crate::W<REG> {
        self.variant(Etfc::FdtsDiv2N6)
    }
    #[doc = "fSAMP=fDTS/2, N=8"]
    #[inline(always)]
    pub fn fdts_div2_n8(self) -> &'a mut crate::W<REG> {
        self.variant(Etfc::FdtsDiv2N8)
    }
    #[doc = "fSAMP=fDTS/4, N=6"]
    #[inline(always)]
    pub fn fdts_div4_n6(self) -> &'a mut crate::W<REG> {
        self.variant(Etfc::FdtsDiv4N6)
    }
    #[doc = "fSAMP=fDTS/4, N=8"]
    #[inline(always)]
    pub fn fdts_div4_n8(self) -> &'a mut crate::W<REG> {
        self.variant(Etfc::FdtsDiv4N8)
    }
    #[doc = "fSAMP=fDTS/8, N=6"]
    #[inline(always)]
    pub fn fdts_div8_n6(self) -> &'a mut crate::W<REG> {
        self.variant(Etfc::FdtsDiv8N6)
    }
    #[doc = "fSAMP=fDTS/8, N=8"]
    #[inline(always)]
    pub fn fdts_div8_n8(self) -> &'a mut crate::W<REG> {
        self.variant(Etfc::FdtsDiv8N8)
    }
    #[doc = "fSAMP=fDTS/16, N=5"]
    #[inline(always)]
    pub fn fdts_div16_n5(self) -> &'a mut crate::W<REG> {
        self.variant(Etfc::FdtsDiv16N5)
    }
    #[doc = "fSAMP=fDTS/16, N=6"]
    #[inline(always)]
    pub fn fdts_div16_n6(self) -> &'a mut crate::W<REG> {
        self.variant(Etfc::FdtsDiv16N6)
    }
    #[doc = "fSAMP=fDTS/16, N=8"]
    #[inline(always)]
    pub fn fdts_div16_n8(self) -> &'a mut crate::W<REG> {
        self.variant(Etfc::FdtsDiv16N8)
    }
    #[doc = "fSAMP=fDTS/32, N=5"]
    #[inline(always)]
    pub fn fdts_div32_n5(self) -> &'a mut crate::W<REG> {
        self.variant(Etfc::FdtsDiv32N5)
    }
    #[doc = "fSAMP=fDTS/32, N=6"]
    #[inline(always)]
    pub fn fdts_div32_n6(self) -> &'a mut crate::W<REG> {
        self.variant(Etfc::FdtsDiv32N6)
    }
    #[doc = "fSAMP=fDTS/32, N=8"]
    #[inline(always)]
    pub fn fdts_div32_n8(self) -> &'a mut crate::W<REG> {
        self.variant(Etfc::FdtsDiv32N8)
    }
}
#[doc = "External trigger prescaler\n\nValue on reset: 0"]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u8)]
pub enum Etpsc {
    #[doc = "0: External trigger prescaler disabled"]
    Div1 = 0,
    #[doc = "1: ETI frequency divided by 2"]
    Div2 = 1,
    #[doc = "2: ETI frequency divided by 4"]
    Div4 = 2,
    #[doc = "3: ETI frequency divided by 8"]
    Div8 = 3,
}
impl From<Etpsc> for u8 {
    #[inline(always)]
    fn from(variant: Etpsc) -> Self {
        variant as _
    }
}
impl crate::FieldSpec for Etpsc {
    type Ux = u8;
}
#[doc = "Field `ETPSC` reader - External trigger prescaler"]
pub type EtpscR = crate::FieldReader<Etpsc>;
impl EtpscR {
    #[doc = "Get enumerated values variant"]
    #[inline(always)]
    pub const fn variant(&self) -> Etpsc {
        match self.bits {
            0 => Etpsc::Div1,
            1 => Etpsc::Div2,
            2 => Etpsc::Div4,
            3 => Etpsc::Div8,
            _ => unreachable!(),
        }
    }
    #[doc = "External trigger prescaler disabled"]
    #[inline(always)]
    pub fn is_div1(&self) -> bool {
        *self == Etpsc::Div1
    }
    #[doc = "ETI frequency divided by 2"]
    #[inline(always)]
    pub fn is_div2(&self) -> bool {
        *self == Etpsc::Div2
    }
    #[doc = "ETI frequency divided by 4"]
    #[inline(always)]
    pub fn is_div4(&self) -> bool {
        *self == Etpsc::Div4
    }
    #[doc = "ETI frequency divided by 8"]
    #[inline(always)]
    pub fn is_div8(&self) -> bool {
        *self == Etpsc::Div8
    }
}
#[doc = "Field `ETPSC` writer - External trigger prescaler"]
pub type EtpscW<'a, REG> = crate::FieldWriterSafe<'a, REG, 2, Etpsc>;
impl<'a, REG> EtpscW<'a, REG>
where
    REG: crate::Writable + crate::RegisterSpec,
    REG::Ux: From<u8>,
{
    #[doc = "External trigger prescaler disabled"]
    #[inline(always)]
    pub fn div1(self) -> &'a mut crate::W<REG> {
        self.variant(Etpsc::Div1)
    }
    #[doc = "ETI frequency divided by 2"]
    #[inline(always)]
    pub fn div2(self) -> &'a mut crate::W<REG> {
        self.variant(Etpsc::Div2)
    }
    #[doc = "ETI frequency divided by 4"]
    #[inline(always)]
    pub fn div4(self) -> &'a mut crate::W<REG> {
        self.variant(Etpsc::Div4)
    }
    #[doc = "ETI frequency divided by 8"]
    #[inline(always)]
    pub fn div8(self) -> &'a mut crate::W<REG> {
        self.variant(Etpsc::Div8)
    }
}
#[doc = "Part of SMC for enable External clock mode1\n\nValue on reset: 0"]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Smc1 {
    #[doc = "0: External clock mode 1 disabled"]
    Disabled = 0,
    #[doc = "1: External clock mode 1 enabled. The counter is clocked by any active edge on the ETIF signal."]
    Enabled = 1,
}
impl From<Smc1> for bool {
    #[inline(always)]
    fn from(variant: Smc1) -> Self {
        variant as u8 != 0
    }
}
#[doc = "Field `SMC1` reader - Part of SMC for enable External clock mode1"]
pub type Smc1R = crate::BitReader<Smc1>;
impl Smc1R {
    #[doc = "Get enumerated values variant"]
    #[inline(always)]
    pub const fn variant(&self) -> Smc1 {
        match self.bits {
            false => Smc1::Disabled,
            true => Smc1::Enabled,
        }
    }
    #[doc = "External clock mode 1 disabled"]
    #[inline(always)]
    pub fn is_disabled(&self) -> bool {
        *self == Smc1::Disabled
    }
    #[doc = "External clock mode 1 enabled. The counter is clocked by any active edge on the ETIF signal."]
    #[inline(always)]
    pub fn is_enabled(&self) -> bool {
        *self == Smc1::Enabled
    }
}
#[doc = "Field `SMC1` writer - Part of SMC for enable External clock mode1"]
pub type Smc1W<'a, REG> = crate::BitWriter<'a, REG, Smc1>;
impl<'a, REG> Smc1W<'a, REG>
where
    REG: crate::Writable + crate::RegisterSpec,
{
    #[doc = "External clock mode 1 disabled"]
    #[inline(always)]
    pub fn disabled(self) -> &'a mut crate::W<REG> {
        self.variant(Smc1::Disabled)
    }
    #[doc = "External clock mode 1 enabled. The counter is clocked by any active edge on the ETIF signal."]
    #[inline(always)]
    pub fn enabled(self) -> &'a mut crate::W<REG> {
        self.variant(Smc1::Enabled)
    }
}
#[doc = "External trigger polarity\n\nValue on reset: 0"]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Etp {
    #[doc = "0: ETI is noninverted, active at high level or rising edge"]
    NotInverted = 0,
    #[doc = "1: ETI is inverted, active at low level or falling edge"]
    Inverted = 1,
}
impl From<Etp> for bool {
    #[inline(always)]
    fn from(variant: Etp) -> Self {
        variant as u8 != 0
    }
}
#[doc = "Field `ETP` reader - External trigger polarity"]
pub type EtpR = crate::BitReader<Etp>;
impl EtpR {
    #[doc = "Get enumerated values variant"]
    #[inline(always)]
    pub const fn variant(&self) -> Etp {
        match self.bits {
            false => Etp::NotInverted,
            true => Etp::Inverted,
        }
    }
    #[doc = "ETI is noninverted, active at high level or rising edge"]
    #[inline(always)]
    pub fn is_not_inverted(&self) -> bool {
        *self == Etp::NotInverted
    }
    #[doc = "ETI is inverted, active at low level or falling edge"]
    #[inline(always)]
    pub fn is_inverted(&self) -> bool {
        *self == Etp::Inverted
    }
}
#[doc = "Field `ETP` writer - External trigger polarity"]
pub type EtpW<'a, REG> = crate::BitWriter<'a, REG, Etp>;
impl<'a, REG> EtpW<'a, REG>
where
    REG: crate::Writable + crate::RegisterSpec,
{
    #[doc = "ETI is noninverted, active at high level or rising edge"]
    #[inline(always)]
    pub fn not_inverted(self) -> &'a mut crate::W<REG> {
        self.variant(Etp::NotInverted)
    }
    #[doc = "ETI is inverted, active at low level or falling edge"]
    #[inline(always)]
    pub fn inverted(self) -> &'a mut crate::W<REG> {
        self.variant(Etp::Inverted)
    }
}
impl R {
    #[doc = "Bits 0:2 - Slave mode control"]
    #[inline(always)]
    pub fn smc(&self) -> SmcR {
        SmcR::new((self.bits & 7) as u8)
    }
    #[doc = "Bits 4:6 - Trigger selection"]
    #[inline(always)]
    pub fn trgs(&self) -> TrgsR {
        TrgsR::new(((self.bits >> 4) & 7) as u8)
    }
    #[doc = "Bit 7 - Master-slave mode"]
    #[inline(always)]
    pub fn msm(&self) -> MsmR {
        MsmR::new(((self.bits >> 7) & 1) != 0)
    }
    #[doc = "Bits 8:11 - External trigger filter control"]
    #[inline(always)]
    pub fn etfc(&self) -> EtfcR {
        EtfcR::new(((self.bits >> 8) & 0x0f) as u8)
    }
    #[doc = "Bits 12:13 - External trigger prescaler"]
    #[inline(always)]
    pub fn etpsc(&self) -> EtpscR {
        EtpscR::new(((self.bits >> 12) & 3) as u8)
    }
    #[doc = "Bit 14 - Part of SMC for enable External clock mode1"]
    #[inline(always)]
    pub fn smc1(&self) -> Smc1R {
        Smc1R::new(((self.bits >> 14) & 1) != 0)
    }
    #[doc = "Bit 15 - External trigger polarity"]
    #[inline(always)]
    pub fn etp(&self) -> EtpR {
        EtpR::new(((self.bits >> 15) & 1) != 0)
    }
}
impl W {
    #[doc = "Bits 0:2 - Slave mode control"]
    #[inline(always)]
    #[must_use]
    pub fn smc(&mut self) -> SmcW<SmcfgSpec> {
        SmcW::new(self, 0)
    }
    #[doc = "Bits 4:6 - Trigger selection"]
    #[inline(always)]
    #[must_use]
    pub fn trgs(&mut self) -> TrgsW<SmcfgSpec> {
        TrgsW::new(self, 4)
    }
    #[doc = "Bit 7 - Master-slave mode"]
    #[inline(always)]
    #[must_use]
    pub fn msm(&mut self) -> MsmW<SmcfgSpec> {
        MsmW::new(self, 7)
    }
    #[doc = "Bits 8:11 - External trigger filter control"]
    #[inline(always)]
    #[must_use]
    pub fn etfc(&mut self) -> EtfcW<SmcfgSpec> {
        EtfcW::new(self, 8)
    }
    #[doc = "Bits 12:13 - External trigger prescaler"]
    #[inline(always)]
    #[must_use]
    pub fn etpsc(&mut self) -> EtpscW<SmcfgSpec> {
        EtpscW::new(self, 12)
    }
    #[doc = "Bit 14 - Part of SMC for enable External clock mode1"]
    #[inline(always)]
    #[must_use]
    pub fn smc1(&mut self) -> Smc1W<SmcfgSpec> {
        Smc1W::new(self, 14)
    }
    #[doc = "Bit 15 - External trigger polarity"]
    #[inline(always)]
    #[must_use]
    pub fn etp(&mut self) -> EtpW<SmcfgSpec> {
        EtpW::new(self, 15)
    }
}
#[doc = "slave mode control register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`smcfg::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`smcfg::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct SmcfgSpec;
impl crate::RegisterSpec for SmcfgSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`smcfg::R`](R) reader structure"]
impl crate::Readable for SmcfgSpec {}
#[doc = "`write(|w| ..)` method takes [`smcfg::W`](W) writer structure"]
impl crate::Writable for SmcfgSpec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets SMCFG to value 0"]
impl crate::Resettable for SmcfgSpec {
    const RESET_VALUE: u32 = 0;
}
