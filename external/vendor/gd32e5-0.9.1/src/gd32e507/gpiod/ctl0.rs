#[doc = "Register `CTL0` reader"]
pub type R = crate::R<Ctl0Spec>;
#[doc = "Register `CTL0` writer"]
pub type W = crate::W<Ctl0Spec>;
#[doc = "Port x mode bits (x = 0)\n\nValue on reset: 0"]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u8)]
pub enum Md0 {
    #[doc = "0: Input mode (reset state)"]
    Input = 0,
    #[doc = "1: Output mode ,max speed 10MHz"]
    Speed10m = 1,
    #[doc = "2: Output mode ,max speed 2MHz"]
    Speed2m = 2,
    #[doc = "3: Output mode ,max speed 50MHz"]
    Speed50m = 3,
}
impl From<Md0> for u8 {
    #[inline(always)]
    fn from(variant: Md0) -> Self {
        variant as _
    }
}
impl crate::FieldSpec for Md0 {
    type Ux = u8;
}
#[doc = "Field `MD0` reader - Port x mode bits (x = 0)"]
pub type Md0R = crate::FieldReader<Md0>;
impl Md0R {
    #[doc = "Get enumerated values variant"]
    #[inline(always)]
    pub const fn variant(&self) -> Md0 {
        match self.bits {
            0 => Md0::Input,
            1 => Md0::Speed10m,
            2 => Md0::Speed2m,
            3 => Md0::Speed50m,
            _ => unreachable!(),
        }
    }
    #[doc = "Input mode (reset state)"]
    #[inline(always)]
    pub fn is_input(&self) -> bool {
        *self == Md0::Input
    }
    #[doc = "Output mode ,max speed 10MHz"]
    #[inline(always)]
    pub fn is_speed10m(&self) -> bool {
        *self == Md0::Speed10m
    }
    #[doc = "Output mode ,max speed 2MHz"]
    #[inline(always)]
    pub fn is_speed2m(&self) -> bool {
        *self == Md0::Speed2m
    }
    #[doc = "Output mode ,max speed 50MHz"]
    #[inline(always)]
    pub fn is_speed50m(&self) -> bool {
        *self == Md0::Speed50m
    }
}
#[doc = "Field `MD0` writer - Port x mode bits (x = 0)"]
pub type Md0W<'a, REG> = crate::FieldWriterSafe<'a, REG, 2, Md0>;
impl<'a, REG> Md0W<'a, REG>
where
    REG: crate::Writable + crate::RegisterSpec,
    REG::Ux: From<u8>,
{
    #[doc = "Input mode (reset state)"]
    #[inline(always)]
    pub fn input(self) -> &'a mut crate::W<REG> {
        self.variant(Md0::Input)
    }
    #[doc = "Output mode ,max speed 10MHz"]
    #[inline(always)]
    pub fn speed10m(self) -> &'a mut crate::W<REG> {
        self.variant(Md0::Speed10m)
    }
    #[doc = "Output mode ,max speed 2MHz"]
    #[inline(always)]
    pub fn speed2m(self) -> &'a mut crate::W<REG> {
        self.variant(Md0::Speed2m)
    }
    #[doc = "Output mode ,max speed 50MHz"]
    #[inline(always)]
    pub fn speed50m(self) -> &'a mut crate::W<REG> {
        self.variant(Md0::Speed50m)
    }
}
#[doc = "Port x configuration bits (x = 0)\n\nValue on reset: 1"]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u8)]
pub enum Ctl0 {
    #[doc = "0: Analog mode/GPIO output with push-pull"]
    AnalogOrPushPull = 0,
    #[doc = "1: Floating input/GPIO output with open-drain"]
    FloatingOrOpenDrain = 1,
    #[doc = "2: Input with pull-up pull-down/AFIO output with push-pull"]
    InputOrAfioPp = 2,
    #[doc = "3: Reserved/AFIO output with open-drain"]
    RsvdorAfioOd = 3,
}
impl From<Ctl0> for u8 {
    #[inline(always)]
    fn from(variant: Ctl0) -> Self {
        variant as _
    }
}
impl crate::FieldSpec for Ctl0 {
    type Ux = u8;
}
#[doc = "Field `CTL0` reader - Port x configuration bits (x = 0)"]
pub type Ctl0R = crate::FieldReader<Ctl0>;
impl Ctl0R {
    #[doc = "Get enumerated values variant"]
    #[inline(always)]
    pub const fn variant(&self) -> Ctl0 {
        match self.bits {
            0 => Ctl0::AnalogOrPushPull,
            1 => Ctl0::FloatingOrOpenDrain,
            2 => Ctl0::InputOrAfioPp,
            3 => Ctl0::RsvdorAfioOd,
            _ => unreachable!(),
        }
    }
    #[doc = "Analog mode/GPIO output with push-pull"]
    #[inline(always)]
    pub fn is_analog_or_push_pull(&self) -> bool {
        *self == Ctl0::AnalogOrPushPull
    }
    #[doc = "Floating input/GPIO output with open-drain"]
    #[inline(always)]
    pub fn is_floating_or_open_drain(&self) -> bool {
        *self == Ctl0::FloatingOrOpenDrain
    }
    #[doc = "Input with pull-up pull-down/AFIO output with push-pull"]
    #[inline(always)]
    pub fn is_input_or_afio_pp(&self) -> bool {
        *self == Ctl0::InputOrAfioPp
    }
    #[doc = "Reserved/AFIO output with open-drain"]
    #[inline(always)]
    pub fn is_rsvdor_afio_od(&self) -> bool {
        *self == Ctl0::RsvdorAfioOd
    }
}
#[doc = "Field `CTL0` writer - Port x configuration bits (x = 0)"]
pub type Ctl0W<'a, REG> = crate::FieldWriterSafe<'a, REG, 2, Ctl0>;
impl<'a, REG> Ctl0W<'a, REG>
where
    REG: crate::Writable + crate::RegisterSpec,
    REG::Ux: From<u8>,
{
    #[doc = "Analog mode/GPIO output with push-pull"]
    #[inline(always)]
    pub fn analog_or_push_pull(self) -> &'a mut crate::W<REG> {
        self.variant(Ctl0::AnalogOrPushPull)
    }
    #[doc = "Floating input/GPIO output with open-drain"]
    #[inline(always)]
    pub fn floating_or_open_drain(self) -> &'a mut crate::W<REG> {
        self.variant(Ctl0::FloatingOrOpenDrain)
    }
    #[doc = "Input with pull-up pull-down/AFIO output with push-pull"]
    #[inline(always)]
    pub fn input_or_afio_pp(self) -> &'a mut crate::W<REG> {
        self.variant(Ctl0::InputOrAfioPp)
    }
    #[doc = "Reserved/AFIO output with open-drain"]
    #[inline(always)]
    pub fn rsvdor_afio_od(self) -> &'a mut crate::W<REG> {
        self.variant(Ctl0::RsvdorAfioOd)
    }
}
#[doc = "Field `CTL1` reader - Port x configuration bits (x = 1)"]
pub use Ctl0R as Ctl1R;
#[doc = "Field `CTL2` reader - Port x configuration bits (x = 2)"]
pub use Ctl0R as Ctl2R;
#[doc = "Field `CTL3` reader - Port x configuration bits (x = 3)"]
pub use Ctl0R as Ctl3R;
#[doc = "Field `CTL4` reader - Port x configuration bits (x = 4)"]
pub use Ctl0R as Ctl4R;
#[doc = "Field `CTL5` reader - Port x configuration bits (x = 5)"]
pub use Ctl0R as Ctl5R;
#[doc = "Field `CTL6` reader - Port x configuration bits (x = 6)"]
pub use Ctl0R as Ctl6R;
#[doc = "Field `CTL7` reader - Port x configuration bits (x = 7)"]
pub use Ctl0R as Ctl7R;
#[doc = "Field `CTL1` writer - Port x configuration bits (x = 1)"]
pub use Ctl0W as Ctl1W;
#[doc = "Field `CTL2` writer - Port x configuration bits (x = 2)"]
pub use Ctl0W as Ctl2W;
#[doc = "Field `CTL3` writer - Port x configuration bits (x = 3)"]
pub use Ctl0W as Ctl3W;
#[doc = "Field `CTL4` writer - Port x configuration bits (x = 4)"]
pub use Ctl0W as Ctl4W;
#[doc = "Field `CTL5` writer - Port x configuration bits (x = 5)"]
pub use Ctl0W as Ctl5W;
#[doc = "Field `CTL6` writer - Port x configuration bits (x = 6)"]
pub use Ctl0W as Ctl6W;
#[doc = "Field `CTL7` writer - Port x configuration bits (x = 7)"]
pub use Ctl0W as Ctl7W;
#[doc = "Field `MD1` reader - Port x mode bits (x = 1)"]
pub use Md0R as Md1R;
#[doc = "Field `MD2` reader - Port x mode bits (x = 2 )"]
pub use Md0R as Md2R;
#[doc = "Field `MD3` reader - Port x mode bits (x = 3 )"]
pub use Md0R as Md3R;
#[doc = "Field `MD4` reader - Port x mode bits (x = 4)"]
pub use Md0R as Md4R;
#[doc = "Field `MD5` reader - Port x mode bits (x = 5)"]
pub use Md0R as Md5R;
#[doc = "Field `MD6` reader - Port x mode bits (x = 6)"]
pub use Md0R as Md6R;
#[doc = "Field `MD7` reader - Port x mode bits (x = 7)"]
pub use Md0R as Md7R;
#[doc = "Field `MD1` writer - Port x mode bits (x = 1)"]
pub use Md0W as Md1W;
#[doc = "Field `MD2` writer - Port x mode bits (x = 2 )"]
pub use Md0W as Md2W;
#[doc = "Field `MD3` writer - Port x mode bits (x = 3 )"]
pub use Md0W as Md3W;
#[doc = "Field `MD4` writer - Port x mode bits (x = 4)"]
pub use Md0W as Md4W;
#[doc = "Field `MD5` writer - Port x mode bits (x = 5)"]
pub use Md0W as Md5W;
#[doc = "Field `MD6` writer - Port x mode bits (x = 6)"]
pub use Md0W as Md6W;
#[doc = "Field `MD7` writer - Port x mode bits (x = 7)"]
pub use Md0W as Md7W;
impl R {
    #[doc = "Bits 0:1 - Port x mode bits (x = 0)"]
    #[inline(always)]
    pub fn md0(&self) -> Md0R {
        Md0R::new((self.bits & 3) as u8)
    }
    #[doc = "Bits 2:3 - Port x configuration bits (x = 0)"]
    #[inline(always)]
    pub fn ctl0(&self) -> Ctl0R {
        Ctl0R::new(((self.bits >> 2) & 3) as u8)
    }
    #[doc = "Bits 4:5 - Port x mode bits (x = 1)"]
    #[inline(always)]
    pub fn md1(&self) -> Md1R {
        Md1R::new(((self.bits >> 4) & 3) as u8)
    }
    #[doc = "Bits 6:7 - Port x configuration bits (x = 1)"]
    #[inline(always)]
    pub fn ctl1(&self) -> Ctl1R {
        Ctl1R::new(((self.bits >> 6) & 3) as u8)
    }
    #[doc = "Bits 8:9 - Port x mode bits (x = 2 )"]
    #[inline(always)]
    pub fn md2(&self) -> Md2R {
        Md2R::new(((self.bits >> 8) & 3) as u8)
    }
    #[doc = "Bits 10:11 - Port x configuration bits (x = 2)"]
    #[inline(always)]
    pub fn ctl2(&self) -> Ctl2R {
        Ctl2R::new(((self.bits >> 10) & 3) as u8)
    }
    #[doc = "Bits 12:13 - Port x mode bits (x = 3 )"]
    #[inline(always)]
    pub fn md3(&self) -> Md3R {
        Md3R::new(((self.bits >> 12) & 3) as u8)
    }
    #[doc = "Bits 14:15 - Port x configuration bits (x = 3)"]
    #[inline(always)]
    pub fn ctl3(&self) -> Ctl3R {
        Ctl3R::new(((self.bits >> 14) & 3) as u8)
    }
    #[doc = "Bits 16:17 - Port x mode bits (x = 4)"]
    #[inline(always)]
    pub fn md4(&self) -> Md4R {
        Md4R::new(((self.bits >> 16) & 3) as u8)
    }
    #[doc = "Bits 18:19 - Port x configuration bits (x = 4)"]
    #[inline(always)]
    pub fn ctl4(&self) -> Ctl4R {
        Ctl4R::new(((self.bits >> 18) & 3) as u8)
    }
    #[doc = "Bits 20:21 - Port x mode bits (x = 5)"]
    #[inline(always)]
    pub fn md5(&self) -> Md5R {
        Md5R::new(((self.bits >> 20) & 3) as u8)
    }
    #[doc = "Bits 22:23 - Port x configuration bits (x = 5)"]
    #[inline(always)]
    pub fn ctl5(&self) -> Ctl5R {
        Ctl5R::new(((self.bits >> 22) & 3) as u8)
    }
    #[doc = "Bits 24:25 - Port x mode bits (x = 6)"]
    #[inline(always)]
    pub fn md6(&self) -> Md6R {
        Md6R::new(((self.bits >> 24) & 3) as u8)
    }
    #[doc = "Bits 26:27 - Port x configuration bits (x = 6)"]
    #[inline(always)]
    pub fn ctl6(&self) -> Ctl6R {
        Ctl6R::new(((self.bits >> 26) & 3) as u8)
    }
    #[doc = "Bits 28:29 - Port x mode bits (x = 7)"]
    #[inline(always)]
    pub fn md7(&self) -> Md7R {
        Md7R::new(((self.bits >> 28) & 3) as u8)
    }
    #[doc = "Bits 30:31 - Port x configuration bits (x = 7)"]
    #[inline(always)]
    pub fn ctl7(&self) -> Ctl7R {
        Ctl7R::new(((self.bits >> 30) & 3) as u8)
    }
}
impl W {
    #[doc = "Bits 0:1 - Port x mode bits (x = 0)"]
    #[inline(always)]
    #[must_use]
    pub fn md0(&mut self) -> Md0W<Ctl0Spec> {
        Md0W::new(self, 0)
    }
    #[doc = "Bits 2:3 - Port x configuration bits (x = 0)"]
    #[inline(always)]
    #[must_use]
    pub fn ctl0(&mut self) -> Ctl0W<Ctl0Spec> {
        Ctl0W::new(self, 2)
    }
    #[doc = "Bits 4:5 - Port x mode bits (x = 1)"]
    #[inline(always)]
    #[must_use]
    pub fn md1(&mut self) -> Md1W<Ctl0Spec> {
        Md1W::new(self, 4)
    }
    #[doc = "Bits 6:7 - Port x configuration bits (x = 1)"]
    #[inline(always)]
    #[must_use]
    pub fn ctl1(&mut self) -> Ctl1W<Ctl0Spec> {
        Ctl1W::new(self, 6)
    }
    #[doc = "Bits 8:9 - Port x mode bits (x = 2 )"]
    #[inline(always)]
    #[must_use]
    pub fn md2(&mut self) -> Md2W<Ctl0Spec> {
        Md2W::new(self, 8)
    }
    #[doc = "Bits 10:11 - Port x configuration bits (x = 2)"]
    #[inline(always)]
    #[must_use]
    pub fn ctl2(&mut self) -> Ctl2W<Ctl0Spec> {
        Ctl2W::new(self, 10)
    }
    #[doc = "Bits 12:13 - Port x mode bits (x = 3 )"]
    #[inline(always)]
    #[must_use]
    pub fn md3(&mut self) -> Md3W<Ctl0Spec> {
        Md3W::new(self, 12)
    }
    #[doc = "Bits 14:15 - Port x configuration bits (x = 3)"]
    #[inline(always)]
    #[must_use]
    pub fn ctl3(&mut self) -> Ctl3W<Ctl0Spec> {
        Ctl3W::new(self, 14)
    }
    #[doc = "Bits 16:17 - Port x mode bits (x = 4)"]
    #[inline(always)]
    #[must_use]
    pub fn md4(&mut self) -> Md4W<Ctl0Spec> {
        Md4W::new(self, 16)
    }
    #[doc = "Bits 18:19 - Port x configuration bits (x = 4)"]
    #[inline(always)]
    #[must_use]
    pub fn ctl4(&mut self) -> Ctl4W<Ctl0Spec> {
        Ctl4W::new(self, 18)
    }
    #[doc = "Bits 20:21 - Port x mode bits (x = 5)"]
    #[inline(always)]
    #[must_use]
    pub fn md5(&mut self) -> Md5W<Ctl0Spec> {
        Md5W::new(self, 20)
    }
    #[doc = "Bits 22:23 - Port x configuration bits (x = 5)"]
    #[inline(always)]
    #[must_use]
    pub fn ctl5(&mut self) -> Ctl5W<Ctl0Spec> {
        Ctl5W::new(self, 22)
    }
    #[doc = "Bits 24:25 - Port x mode bits (x = 6)"]
    #[inline(always)]
    #[must_use]
    pub fn md6(&mut self) -> Md6W<Ctl0Spec> {
        Md6W::new(self, 24)
    }
    #[doc = "Bits 26:27 - Port x configuration bits (x = 6)"]
    #[inline(always)]
    #[must_use]
    pub fn ctl6(&mut self) -> Ctl6W<Ctl0Spec> {
        Ctl6W::new(self, 26)
    }
    #[doc = "Bits 28:29 - Port x mode bits (x = 7)"]
    #[inline(always)]
    #[must_use]
    pub fn md7(&mut self) -> Md7W<Ctl0Spec> {
        Md7W::new(self, 28)
    }
    #[doc = "Bits 30:31 - Port x configuration bits (x = 7)"]
    #[inline(always)]
    #[must_use]
    pub fn ctl7(&mut self) -> Ctl7W<Ctl0Spec> {
        Ctl7W::new(self, 30)
    }
}
#[doc = "port control register 0\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`ctl0::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`ctl0::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
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
#[doc = "`reset()` method sets CTL0 to value 0x4444_4444"]
impl crate::Resettable for Ctl0Spec {
    const RESET_VALUE: u32 = 0x4444_4444;
}
