#[doc = "Register `CTL0` reader"]
pub type R = crate::R<Ctl0Spec>;
#[doc = "Register `CTL0` writer"]
pub type W = crate::W<Ctl0Spec>;
#[doc = "Counter enable\n\nValue on reset: 0"]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Cen {
    #[doc = "0: Counter disabled"]
    Disabled = 0,
    #[doc = "1: Counter enabled"]
    Enabled = 1,
}
impl From<Cen> for bool {
    #[inline(always)]
    fn from(variant: Cen) -> Self {
        variant as u8 != 0
    }
}
#[doc = "Field `CEN` reader - Counter enable"]
pub type CenR = crate::BitReader<Cen>;
impl CenR {
    #[doc = "Get enumerated values variant"]
    #[inline(always)]
    pub const fn variant(&self) -> Cen {
        match self.bits {
            false => Cen::Disabled,
            true => Cen::Enabled,
        }
    }
    #[doc = "Counter disabled"]
    #[inline(always)]
    pub fn is_disabled(&self) -> bool {
        *self == Cen::Disabled
    }
    #[doc = "Counter enabled"]
    #[inline(always)]
    pub fn is_enabled(&self) -> bool {
        *self == Cen::Enabled
    }
}
#[doc = "Field `CEN` writer - Counter enable"]
pub type CenW<'a, REG> = crate::BitWriter<'a, REG, Cen>;
impl<'a, REG> CenW<'a, REG>
where
    REG: crate::Writable + crate::RegisterSpec,
{
    #[doc = "Counter disabled"]
    #[inline(always)]
    pub fn disabled(self) -> &'a mut crate::W<REG> {
        self.variant(Cen::Disabled)
    }
    #[doc = "Counter enabled"]
    #[inline(always)]
    pub fn enabled(self) -> &'a mut crate::W<REG> {
        self.variant(Cen::Enabled)
    }
}
#[doc = "Update disable\n\nValue on reset: 0"]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Updis {
    #[doc = "0: Update event enabled"]
    Enabled = 0,
    #[doc = "1: Update event disabled"]
    Disabled = 1,
}
impl From<Updis> for bool {
    #[inline(always)]
    fn from(variant: Updis) -> Self {
        variant as u8 != 0
    }
}
#[doc = "Field `UPDIS` reader - Update disable"]
pub type UpdisR = crate::BitReader<Updis>;
impl UpdisR {
    #[doc = "Get enumerated values variant"]
    #[inline(always)]
    pub const fn variant(&self) -> Updis {
        match self.bits {
            false => Updis::Enabled,
            true => Updis::Disabled,
        }
    }
    #[doc = "Update event enabled"]
    #[inline(always)]
    pub fn is_enabled(&self) -> bool {
        *self == Updis::Enabled
    }
    #[doc = "Update event disabled"]
    #[inline(always)]
    pub fn is_disabled(&self) -> bool {
        *self == Updis::Disabled
    }
}
#[doc = "Field `UPDIS` writer - Update disable"]
pub type UpdisW<'a, REG> = crate::BitWriter<'a, REG, Updis>;
impl<'a, REG> UpdisW<'a, REG>
where
    REG: crate::Writable + crate::RegisterSpec,
{
    #[doc = "Update event enabled"]
    #[inline(always)]
    pub fn enabled(self) -> &'a mut crate::W<REG> {
        self.variant(Updis::Enabled)
    }
    #[doc = "Update event disabled"]
    #[inline(always)]
    pub fn disabled(self) -> &'a mut crate::W<REG> {
        self.variant(Updis::Disabled)
    }
}
#[doc = "Update source\n\nValue on reset: 0"]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Ups {
    #[doc = "0: Any of counter overflow/underflow, setting UPG, or update through slave mode, generates an update interrupt or DMA request"]
    AnyEvent = 0,
    #[doc = "1: Only counter overflow/underflow generates an update interrupt or DMA request"]
    CounterOnly = 1,
}
impl From<Ups> for bool {
    #[inline(always)]
    fn from(variant: Ups) -> Self {
        variant as u8 != 0
    }
}
#[doc = "Field `UPS` reader - Update source"]
pub type UpsR = crate::BitReader<Ups>;
impl UpsR {
    #[doc = "Get enumerated values variant"]
    #[inline(always)]
    pub const fn variant(&self) -> Ups {
        match self.bits {
            false => Ups::AnyEvent,
            true => Ups::CounterOnly,
        }
    }
    #[doc = "Any of counter overflow/underflow, setting UPG, or update through slave mode, generates an update interrupt or DMA request"]
    #[inline(always)]
    pub fn is_any_event(&self) -> bool {
        *self == Ups::AnyEvent
    }
    #[doc = "Only counter overflow/underflow generates an update interrupt or DMA request"]
    #[inline(always)]
    pub fn is_counter_only(&self) -> bool {
        *self == Ups::CounterOnly
    }
}
#[doc = "Field `UPS` writer - Update source"]
pub type UpsW<'a, REG> = crate::BitWriter<'a, REG, Ups>;
impl<'a, REG> UpsW<'a, REG>
where
    REG: crate::Writable + crate::RegisterSpec,
{
    #[doc = "Any of counter overflow/underflow, setting UPG, or update through slave mode, generates an update interrupt or DMA request"]
    #[inline(always)]
    pub fn any_event(self) -> &'a mut crate::W<REG> {
        self.variant(Ups::AnyEvent)
    }
    #[doc = "Only counter overflow/underflow generates an update interrupt or DMA request"]
    #[inline(always)]
    pub fn counter_only(self) -> &'a mut crate::W<REG> {
        self.variant(Ups::CounterOnly)
    }
}
#[doc = "Single pulse mode\n\nValue on reset: 0"]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Spm {
    #[doc = "0: Counter is not stopped at update event"]
    Disabled = 0,
    #[doc = "1: Counter stops counting at the next update event (clearing the CEN bit)"]
    Enabled = 1,
}
impl From<Spm> for bool {
    #[inline(always)]
    fn from(variant: Spm) -> Self {
        variant as u8 != 0
    }
}
#[doc = "Field `SPM` reader - Single pulse mode"]
pub type SpmR = crate::BitReader<Spm>;
impl SpmR {
    #[doc = "Get enumerated values variant"]
    #[inline(always)]
    pub const fn variant(&self) -> Spm {
        match self.bits {
            false => Spm::Disabled,
            true => Spm::Enabled,
        }
    }
    #[doc = "Counter is not stopped at update event"]
    #[inline(always)]
    pub fn is_disabled(&self) -> bool {
        *self == Spm::Disabled
    }
    #[doc = "Counter stops counting at the next update event (clearing the CEN bit)"]
    #[inline(always)]
    pub fn is_enabled(&self) -> bool {
        *self == Spm::Enabled
    }
}
#[doc = "Field `SPM` writer - Single pulse mode"]
pub type SpmW<'a, REG> = crate::BitWriter<'a, REG, Spm>;
impl<'a, REG> SpmW<'a, REG>
where
    REG: crate::Writable + crate::RegisterSpec,
{
    #[doc = "Counter is not stopped at update event"]
    #[inline(always)]
    pub fn disabled(self) -> &'a mut crate::W<REG> {
        self.variant(Spm::Disabled)
    }
    #[doc = "Counter stops counting at the next update event (clearing the CEN bit)"]
    #[inline(always)]
    pub fn enabled(self) -> &'a mut crate::W<REG> {
        self.variant(Spm::Enabled)
    }
}
#[doc = "Direction\n\nValue on reset: 0"]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Dir {
    #[doc = "0: Counter used as upcounter"]
    Up = 0,
    #[doc = "1: Counter used as downcounter"]
    Down = 1,
}
impl From<Dir> for bool {
    #[inline(always)]
    fn from(variant: Dir) -> Self {
        variant as u8 != 0
    }
}
#[doc = "Field `DIR` reader - Direction"]
pub type DirR = crate::BitReader<Dir>;
impl DirR {
    #[doc = "Get enumerated values variant"]
    #[inline(always)]
    pub const fn variant(&self) -> Dir {
        match self.bits {
            false => Dir::Up,
            true => Dir::Down,
        }
    }
    #[doc = "Counter used as upcounter"]
    #[inline(always)]
    pub fn is_up(&self) -> bool {
        *self == Dir::Up
    }
    #[doc = "Counter used as downcounter"]
    #[inline(always)]
    pub fn is_down(&self) -> bool {
        *self == Dir::Down
    }
}
#[doc = "Field `DIR` writer - Direction"]
pub type DirW<'a, REG> = crate::BitWriter<'a, REG, Dir>;
impl<'a, REG> DirW<'a, REG>
where
    REG: crate::Writable + crate::RegisterSpec,
{
    #[doc = "Counter used as upcounter"]
    #[inline(always)]
    pub fn up(self) -> &'a mut crate::W<REG> {
        self.variant(Dir::Up)
    }
    #[doc = "Counter used as downcounter"]
    #[inline(always)]
    pub fn down(self) -> &'a mut crate::W<REG> {
        self.variant(Dir::Down)
    }
}
#[doc = "Counter aligns mode selection\n\nValue on reset: 0"]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u8)]
pub enum Cam {
    #[doc = "0: The counter counts up or down depending on the direction bit"]
    EdgeAligned = 0,
    #[doc = "1: The counter counts up and down alternatively. Output compare interrupt flags are set only when the counter is counting down."]
    CenterAlignedCountingDown = 1,
    #[doc = "2: The counter counts up and down alternatively. Output compare interrupt flags are set only when the counter is counting up."]
    CenterAlignedCountingUp = 2,
    #[doc = "3: The counter counts up and down alternatively. Output compare interrupt flags are set both when the counter is counting up or down."]
    CenterAlignedCountingUpDown = 3,
}
impl From<Cam> for u8 {
    #[inline(always)]
    fn from(variant: Cam) -> Self {
        variant as _
    }
}
impl crate::FieldSpec for Cam {
    type Ux = u8;
}
#[doc = "Field `CAM` reader - Counter aligns mode selection"]
pub type CamR = crate::FieldReader<Cam>;
impl CamR {
    #[doc = "Get enumerated values variant"]
    #[inline(always)]
    pub const fn variant(&self) -> Cam {
        match self.bits {
            0 => Cam::EdgeAligned,
            1 => Cam::CenterAlignedCountingDown,
            2 => Cam::CenterAlignedCountingUp,
            3 => Cam::CenterAlignedCountingUpDown,
            _ => unreachable!(),
        }
    }
    #[doc = "The counter counts up or down depending on the direction bit"]
    #[inline(always)]
    pub fn is_edge_aligned(&self) -> bool {
        *self == Cam::EdgeAligned
    }
    #[doc = "The counter counts up and down alternatively. Output compare interrupt flags are set only when the counter is counting down."]
    #[inline(always)]
    pub fn is_center_aligned_counting_down(&self) -> bool {
        *self == Cam::CenterAlignedCountingDown
    }
    #[doc = "The counter counts up and down alternatively. Output compare interrupt flags are set only when the counter is counting up."]
    #[inline(always)]
    pub fn is_center_aligned_counting_up(&self) -> bool {
        *self == Cam::CenterAlignedCountingUp
    }
    #[doc = "The counter counts up and down alternatively. Output compare interrupt flags are set both when the counter is counting up or down."]
    #[inline(always)]
    pub fn is_center_aligned_counting_up_down(&self) -> bool {
        *self == Cam::CenterAlignedCountingUpDown
    }
}
#[doc = "Field `CAM` writer - Counter aligns mode selection"]
pub type CamW<'a, REG> = crate::FieldWriterSafe<'a, REG, 2, Cam>;
impl<'a, REG> CamW<'a, REG>
where
    REG: crate::Writable + crate::RegisterSpec,
    REG::Ux: From<u8>,
{
    #[doc = "The counter counts up or down depending on the direction bit"]
    #[inline(always)]
    pub fn edge_aligned(self) -> &'a mut crate::W<REG> {
        self.variant(Cam::EdgeAligned)
    }
    #[doc = "The counter counts up and down alternatively. Output compare interrupt flags are set only when the counter is counting down."]
    #[inline(always)]
    pub fn center_aligned_counting_down(self) -> &'a mut crate::W<REG> {
        self.variant(Cam::CenterAlignedCountingDown)
    }
    #[doc = "The counter counts up and down alternatively. Output compare interrupt flags are set only when the counter is counting up."]
    #[inline(always)]
    pub fn center_aligned_counting_up(self) -> &'a mut crate::W<REG> {
        self.variant(Cam::CenterAlignedCountingUp)
    }
    #[doc = "The counter counts up and down alternatively. Output compare interrupt flags are set both when the counter is counting up or down."]
    #[inline(always)]
    pub fn center_aligned_counting_up_down(self) -> &'a mut crate::W<REG> {
        self.variant(Cam::CenterAlignedCountingUpDown)
    }
}
#[doc = "Auto-reload shadow enable\n\nValue on reset: 0"]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Arse {
    #[doc = "0: The shadow register for CAR is disabled"]
    Disabled = 0,
    #[doc = "1: The shadow register for CAR is enabled"]
    Enabled = 1,
}
impl From<Arse> for bool {
    #[inline(always)]
    fn from(variant: Arse) -> Self {
        variant as u8 != 0
    }
}
#[doc = "Field `ARSE` reader - Auto-reload shadow enable"]
pub type ArseR = crate::BitReader<Arse>;
impl ArseR {
    #[doc = "Get enumerated values variant"]
    #[inline(always)]
    pub const fn variant(&self) -> Arse {
        match self.bits {
            false => Arse::Disabled,
            true => Arse::Enabled,
        }
    }
    #[doc = "The shadow register for CAR is disabled"]
    #[inline(always)]
    pub fn is_disabled(&self) -> bool {
        *self == Arse::Disabled
    }
    #[doc = "The shadow register for CAR is enabled"]
    #[inline(always)]
    pub fn is_enabled(&self) -> bool {
        *self == Arse::Enabled
    }
}
#[doc = "Field `ARSE` writer - Auto-reload shadow enable"]
pub type ArseW<'a, REG> = crate::BitWriter<'a, REG, Arse>;
impl<'a, REG> ArseW<'a, REG>
where
    REG: crate::Writable + crate::RegisterSpec,
{
    #[doc = "The shadow register for CAR is disabled"]
    #[inline(always)]
    pub fn disabled(self) -> &'a mut crate::W<REG> {
        self.variant(Arse::Disabled)
    }
    #[doc = "The shadow register for CAR is enabled"]
    #[inline(always)]
    pub fn enabled(self) -> &'a mut crate::W<REG> {
        self.variant(Arse::Enabled)
    }
}
#[doc = "Clock division\n\nValue on reset: 0"]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u8)]
pub enum Ckdiv {
    #[doc = "0: t_DTS = t_CK_INT"]
    Div1 = 0,
    #[doc = "1: t_DTS = 2 × t_CK_INT"]
    Div2 = 1,
    #[doc = "2: t_DTS = 4 × t_CK_INT"]
    Div4 = 2,
}
impl From<Ckdiv> for u8 {
    #[inline(always)]
    fn from(variant: Ckdiv) -> Self {
        variant as _
    }
}
impl crate::FieldSpec for Ckdiv {
    type Ux = u8;
}
#[doc = "Field `CKDIV` reader - Clock division"]
pub type CkdivR = crate::FieldReader<Ckdiv>;
impl CkdivR {
    #[doc = "Get enumerated values variant"]
    #[inline(always)]
    pub const fn variant(&self) -> Option<Ckdiv> {
        match self.bits {
            0 => Some(Ckdiv::Div1),
            1 => Some(Ckdiv::Div2),
            2 => Some(Ckdiv::Div4),
            _ => None,
        }
    }
    #[doc = "t_DTS = t_CK_INT"]
    #[inline(always)]
    pub fn is_div1(&self) -> bool {
        *self == Ckdiv::Div1
    }
    #[doc = "t_DTS = 2 × t_CK_INT"]
    #[inline(always)]
    pub fn is_div2(&self) -> bool {
        *self == Ckdiv::Div2
    }
    #[doc = "t_DTS = 4 × t_CK_INT"]
    #[inline(always)]
    pub fn is_div4(&self) -> bool {
        *self == Ckdiv::Div4
    }
}
#[doc = "Field `CKDIV` writer - Clock division"]
pub type CkdivW<'a, REG> = crate::FieldWriter<'a, REG, 2, Ckdiv>;
impl<'a, REG> CkdivW<'a, REG>
where
    REG: crate::Writable + crate::RegisterSpec,
    REG::Ux: From<u8>,
{
    #[doc = "t_DTS = t_CK_INT"]
    #[inline(always)]
    pub fn div1(self) -> &'a mut crate::W<REG> {
        self.variant(Ckdiv::Div1)
    }
    #[doc = "t_DTS = 2 × t_CK_INT"]
    #[inline(always)]
    pub fn div2(self) -> &'a mut crate::W<REG> {
        self.variant(Ckdiv::Div2)
    }
    #[doc = "t_DTS = 4 × t_CK_INT"]
    #[inline(always)]
    pub fn div4(self) -> &'a mut crate::W<REG> {
        self.variant(Ckdiv::Div4)
    }
}
impl R {
    #[doc = "Bit 0 - Counter enable"]
    #[inline(always)]
    pub fn cen(&self) -> CenR {
        CenR::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - Update disable"]
    #[inline(always)]
    pub fn updis(&self) -> UpdisR {
        UpdisR::new(((self.bits >> 1) & 1) != 0)
    }
    #[doc = "Bit 2 - Update source"]
    #[inline(always)]
    pub fn ups(&self) -> UpsR {
        UpsR::new(((self.bits >> 2) & 1) != 0)
    }
    #[doc = "Bit 3 - Single pulse mode"]
    #[inline(always)]
    pub fn spm(&self) -> SpmR {
        SpmR::new(((self.bits >> 3) & 1) != 0)
    }
    #[doc = "Bit 4 - Direction"]
    #[inline(always)]
    pub fn dir(&self) -> DirR {
        DirR::new(((self.bits >> 4) & 1) != 0)
    }
    #[doc = "Bits 5:6 - Counter aligns mode selection"]
    #[inline(always)]
    pub fn cam(&self) -> CamR {
        CamR::new(((self.bits >> 5) & 3) as u8)
    }
    #[doc = "Bit 7 - Auto-reload shadow enable"]
    #[inline(always)]
    pub fn arse(&self) -> ArseR {
        ArseR::new(((self.bits >> 7) & 1) != 0)
    }
    #[doc = "Bits 8:9 - Clock division"]
    #[inline(always)]
    pub fn ckdiv(&self) -> CkdivR {
        CkdivR::new(((self.bits >> 8) & 3) as u8)
    }
}
impl W {
    #[doc = "Bit 0 - Counter enable"]
    #[inline(always)]
    #[must_use]
    pub fn cen(&mut self) -> CenW<Ctl0Spec> {
        CenW::new(self, 0)
    }
    #[doc = "Bit 1 - Update disable"]
    #[inline(always)]
    #[must_use]
    pub fn updis(&mut self) -> UpdisW<Ctl0Spec> {
        UpdisW::new(self, 1)
    }
    #[doc = "Bit 2 - Update source"]
    #[inline(always)]
    #[must_use]
    pub fn ups(&mut self) -> UpsW<Ctl0Spec> {
        UpsW::new(self, 2)
    }
    #[doc = "Bit 3 - Single pulse mode"]
    #[inline(always)]
    #[must_use]
    pub fn spm(&mut self) -> SpmW<Ctl0Spec> {
        SpmW::new(self, 3)
    }
    #[doc = "Bit 4 - Direction"]
    #[inline(always)]
    #[must_use]
    pub fn dir(&mut self) -> DirW<Ctl0Spec> {
        DirW::new(self, 4)
    }
    #[doc = "Bits 5:6 - Counter aligns mode selection"]
    #[inline(always)]
    #[must_use]
    pub fn cam(&mut self) -> CamW<Ctl0Spec> {
        CamW::new(self, 5)
    }
    #[doc = "Bit 7 - Auto-reload shadow enable"]
    #[inline(always)]
    #[must_use]
    pub fn arse(&mut self) -> ArseW<Ctl0Spec> {
        ArseW::new(self, 7)
    }
    #[doc = "Bits 8:9 - Clock division"]
    #[inline(always)]
    #[must_use]
    pub fn ckdiv(&mut self) -> CkdivW<Ctl0Spec> {
        CkdivW::new(self, 8)
    }
}
#[doc = "control register 0\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`ctl0::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`ctl0::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct Ctl0Spec;
impl crate::RegisterSpec for Ctl0Spec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`ctl0::R`](R) reader structure"]
impl crate::Readable for Ctl0Spec {}
#[doc = "`write(|w| ..)` method takes [`ctl0::W`](W) writer structure"]
impl crate::Writable for Ctl0Spec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets CTL0 to value 0"]
impl crate::Resettable for Ctl0Spec {
    const RESET_VALUE: u32 = 0;
}
