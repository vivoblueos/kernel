#[doc = "Register `CTL1` reader"]
pub type R = crate::R<Ctl1Spec>;
#[doc = "Register `CTL1` writer"]
pub type W = crate::W<Ctl1Spec>;
#[doc = "Port x mode bits (x = 8)\n\nValue on reset: 0"]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u8)]
pub enum Md8 {
    #[doc = "0: Input mode (reset state)"]
    Input = 0,
    #[doc = "1: Output mode ,max speed 10MHz"]
    Speed10m = 1,
    #[doc = "2: Output mode ,max speed 2MHz"]
    Speed2m = 2,
    #[doc = "3: Output mode ,max speed 50MHz"]
    Speed50m = 3,
}
impl From<Md8> for u8 {
    #[inline(always)]
    fn from(variant: Md8) -> Self {
        variant as _
    }
}
impl crate::FieldSpec for Md8 {
    type Ux = u8;
}
#[doc = "Field `MD8` reader - Port x mode bits (x = 8)"]
pub type Md8R = crate::FieldReader<Md8>;
impl Md8R {
    #[doc = "Get enumerated values variant"]
    #[inline(always)]
    pub const fn variant(&self) -> Md8 {
        match self.bits {
            0 => Md8::Input,
            1 => Md8::Speed10m,
            2 => Md8::Speed2m,
            3 => Md8::Speed50m,
            _ => unreachable!(),
        }
    }
    #[doc = "Input mode (reset state)"]
    #[inline(always)]
    pub fn is_input(&self) -> bool {
        *self == Md8::Input
    }
    #[doc = "Output mode ,max speed 10MHz"]
    #[inline(always)]
    pub fn is_speed10m(&self) -> bool {
        *self == Md8::Speed10m
    }
    #[doc = "Output mode ,max speed 2MHz"]
    #[inline(always)]
    pub fn is_speed2m(&self) -> bool {
        *self == Md8::Speed2m
    }
    #[doc = "Output mode ,max speed 50MHz"]
    #[inline(always)]
    pub fn is_speed50m(&self) -> bool {
        *self == Md8::Speed50m
    }
}
#[doc = "Field `MD8` writer - Port x mode bits (x = 8)"]
pub type Md8W<'a, REG> = crate::FieldWriterSafe<'a, REG, 2, Md8>;
impl<'a, REG> Md8W<'a, REG>
where
    REG: crate::Writable + crate::RegisterSpec,
    REG::Ux: From<u8>,
{
    #[doc = "Input mode (reset state)"]
    #[inline(always)]
    pub fn input(self) -> &'a mut crate::W<REG> {
        self.variant(Md8::Input)
    }
    #[doc = "Output mode ,max speed 10MHz"]
    #[inline(always)]
    pub fn speed10m(self) -> &'a mut crate::W<REG> {
        self.variant(Md8::Speed10m)
    }
    #[doc = "Output mode ,max speed 2MHz"]
    #[inline(always)]
    pub fn speed2m(self) -> &'a mut crate::W<REG> {
        self.variant(Md8::Speed2m)
    }
    #[doc = "Output mode ,max speed 50MHz"]
    #[inline(always)]
    pub fn speed50m(self) -> &'a mut crate::W<REG> {
        self.variant(Md8::Speed50m)
    }
}
#[doc = "Port x configuration bits (x = 8)\n\nValue on reset: 1"]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u8)]
pub enum Ctl8 {
    #[doc = "0: Analog mode/GPIO output with push-pull"]
    AnalogOrPushPull = 0,
    #[doc = "1: Floating input/GPIO output with open-drain"]
    FloatingOrOpenDrain = 1,
    #[doc = "2: Input with pull-up pull-down/AFIO output with push-pull"]
    InputOrAfioPp = 2,
    #[doc = "3: Reserved/AFIO output with open-drain"]
    RsvdorAfioOd = 3,
}
impl From<Ctl8> for u8 {
    #[inline(always)]
    fn from(variant: Ctl8) -> Self {
        variant as _
    }
}
impl crate::FieldSpec for Ctl8 {
    type Ux = u8;
}
#[doc = "Field `CTL8` reader - Port x configuration bits (x = 8)"]
pub type Ctl8R = crate::FieldReader<Ctl8>;
impl Ctl8R {
    #[doc = "Get enumerated values variant"]
    #[inline(always)]
    pub const fn variant(&self) -> Ctl8 {
        match self.bits {
            0 => Ctl8::AnalogOrPushPull,
            1 => Ctl8::FloatingOrOpenDrain,
            2 => Ctl8::InputOrAfioPp,
            3 => Ctl8::RsvdorAfioOd,
            _ => unreachable!(),
        }
    }
    #[doc = "Analog mode/GPIO output with push-pull"]
    #[inline(always)]
    pub fn is_analog_or_push_pull(&self) -> bool {
        *self == Ctl8::AnalogOrPushPull
    }
    #[doc = "Floating input/GPIO output with open-drain"]
    #[inline(always)]
    pub fn is_floating_or_open_drain(&self) -> bool {
        *self == Ctl8::FloatingOrOpenDrain
    }
    #[doc = "Input with pull-up pull-down/AFIO output with push-pull"]
    #[inline(always)]
    pub fn is_input_or_afio_pp(&self) -> bool {
        *self == Ctl8::InputOrAfioPp
    }
    #[doc = "Reserved/AFIO output with open-drain"]
    #[inline(always)]
    pub fn is_rsvdor_afio_od(&self) -> bool {
        *self == Ctl8::RsvdorAfioOd
    }
}
#[doc = "Field `CTL8` writer - Port x configuration bits (x = 8)"]
pub type Ctl8W<'a, REG> = crate::FieldWriterSafe<'a, REG, 2, Ctl8>;
impl<'a, REG> Ctl8W<'a, REG>
where
    REG: crate::Writable + crate::RegisterSpec,
    REG::Ux: From<u8>,
{
    #[doc = "Analog mode/GPIO output with push-pull"]
    #[inline(always)]
    pub fn analog_or_push_pull(self) -> &'a mut crate::W<REG> {
        self.variant(Ctl8::AnalogOrPushPull)
    }
    #[doc = "Floating input/GPIO output with open-drain"]
    #[inline(always)]
    pub fn floating_or_open_drain(self) -> &'a mut crate::W<REG> {
        self.variant(Ctl8::FloatingOrOpenDrain)
    }
    #[doc = "Input with pull-up pull-down/AFIO output with push-pull"]
    #[inline(always)]
    pub fn input_or_afio_pp(self) -> &'a mut crate::W<REG> {
        self.variant(Ctl8::InputOrAfioPp)
    }
    #[doc = "Reserved/AFIO output with open-drain"]
    #[inline(always)]
    pub fn rsvdor_afio_od(self) -> &'a mut crate::W<REG> {
        self.variant(Ctl8::RsvdorAfioOd)
    }
}
#[doc = "Field `CTL9` reader - Port x configuration bits (x = 9)"]
pub use Ctl8R as Ctl9R;
#[doc = "Field `CTL10` reader - Port x configuration bits (x = 10)"]
pub use Ctl8R as Ctl10R;
#[doc = "Field `CTL11` reader - Port x configuration bits (x = 11)"]
pub use Ctl8R as Ctl11R;
#[doc = "Field `CTL12` reader - Port x configuration bits (x = 12)"]
pub use Ctl8R as Ctl12R;
#[doc = "Field `CTL13` reader - Port x configuration bits (x = 13)"]
pub use Ctl8R as Ctl13R;
#[doc = "Field `CTL14` reader - Port x configuration bits (x = 14)"]
pub use Ctl8R as Ctl14R;
#[doc = "Field `CTL15` reader - Port x configuration bits (x = 15)"]
pub use Ctl8R as Ctl15R;
#[doc = "Field `CTL9` writer - Port x configuration bits (x = 9)"]
pub use Ctl8W as Ctl9W;
#[doc = "Field `CTL10` writer - Port x configuration bits (x = 10)"]
pub use Ctl8W as Ctl10W;
#[doc = "Field `CTL11` writer - Port x configuration bits (x = 11)"]
pub use Ctl8W as Ctl11W;
#[doc = "Field `CTL12` writer - Port x configuration bits (x = 12)"]
pub use Ctl8W as Ctl12W;
#[doc = "Field `CTL13` writer - Port x configuration bits (x = 13)"]
pub use Ctl8W as Ctl13W;
#[doc = "Field `CTL14` writer - Port x configuration bits (x = 14)"]
pub use Ctl8W as Ctl14W;
#[doc = "Field `CTL15` writer - Port x configuration bits (x = 15)"]
pub use Ctl8W as Ctl15W;
#[doc = "Field `MD9` reader - Port x mode bits (x = 9)"]
pub use Md8R as Md9R;
#[doc = "Field `MD10` reader - Port x mode bits (x = 10 )"]
pub use Md8R as Md10R;
#[doc = "Field `MD11` reader - Port x mode bits (x = 11 )"]
pub use Md8R as Md11R;
#[doc = "Field `MD12` reader - Port x mode bits (x = 12)"]
pub use Md8R as Md12R;
#[doc = "Field `MD13` reader - Port x mode bits (x = 13)"]
pub use Md8R as Md13R;
#[doc = "Field `MD14` reader - Port x mode bits (x = 14)"]
pub use Md8R as Md14R;
#[doc = "Field `MD15` reader - Port x mode bits (x = 15)"]
pub use Md8R as Md15R;
#[doc = "Field `MD9` writer - Port x mode bits (x = 9)"]
pub use Md8W as Md9W;
#[doc = "Field `MD10` writer - Port x mode bits (x = 10 )"]
pub use Md8W as Md10W;
#[doc = "Field `MD11` writer - Port x mode bits (x = 11 )"]
pub use Md8W as Md11W;
#[doc = "Field `MD12` writer - Port x mode bits (x = 12)"]
pub use Md8W as Md12W;
#[doc = "Field `MD13` writer - Port x mode bits (x = 13)"]
pub use Md8W as Md13W;
#[doc = "Field `MD14` writer - Port x mode bits (x = 14)"]
pub use Md8W as Md14W;
#[doc = "Field `MD15` writer - Port x mode bits (x = 15)"]
pub use Md8W as Md15W;
impl R {
    #[doc = "Bits 0:1 - Port x mode bits (x = 8)"]
    #[inline(always)]
    pub fn md8(&self) -> Md8R {
        Md8R::new((self.bits & 3) as u8)
    }
    #[doc = "Bits 2:3 - Port x configuration bits (x = 8)"]
    #[inline(always)]
    pub fn ctl8(&self) -> Ctl8R {
        Ctl8R::new(((self.bits >> 2) & 3) as u8)
    }
    #[doc = "Bits 4:5 - Port x mode bits (x = 9)"]
    #[inline(always)]
    pub fn md9(&self) -> Md9R {
        Md9R::new(((self.bits >> 4) & 3) as u8)
    }
    #[doc = "Bits 6:7 - Port x configuration bits (x = 9)"]
    #[inline(always)]
    pub fn ctl9(&self) -> Ctl9R {
        Ctl9R::new(((self.bits >> 6) & 3) as u8)
    }
    #[doc = "Bits 8:9 - Port x mode bits (x = 10 )"]
    #[inline(always)]
    pub fn md10(&self) -> Md10R {
        Md10R::new(((self.bits >> 8) & 3) as u8)
    }
    #[doc = "Bits 10:11 - Port x configuration bits (x = 10)"]
    #[inline(always)]
    pub fn ctl10(&self) -> Ctl10R {
        Ctl10R::new(((self.bits >> 10) & 3) as u8)
    }
    #[doc = "Bits 12:13 - Port x mode bits (x = 11 )"]
    #[inline(always)]
    pub fn md11(&self) -> Md11R {
        Md11R::new(((self.bits >> 12) & 3) as u8)
    }
    #[doc = "Bits 14:15 - Port x configuration bits (x = 11)"]
    #[inline(always)]
    pub fn ctl11(&self) -> Ctl11R {
        Ctl11R::new(((self.bits >> 14) & 3) as u8)
    }
    #[doc = "Bits 16:17 - Port x mode bits (x = 12)"]
    #[inline(always)]
    pub fn md12(&self) -> Md12R {
        Md12R::new(((self.bits >> 16) & 3) as u8)
    }
    #[doc = "Bits 18:19 - Port x configuration bits (x = 12)"]
    #[inline(always)]
    pub fn ctl12(&self) -> Ctl12R {
        Ctl12R::new(((self.bits >> 18) & 3) as u8)
    }
    #[doc = "Bits 20:21 - Port x mode bits (x = 13)"]
    #[inline(always)]
    pub fn md13(&self) -> Md13R {
        Md13R::new(((self.bits >> 20) & 3) as u8)
    }
    #[doc = "Bits 22:23 - Port x configuration bits (x = 13)"]
    #[inline(always)]
    pub fn ctl13(&self) -> Ctl13R {
        Ctl13R::new(((self.bits >> 22) & 3) as u8)
    }
    #[doc = "Bits 24:25 - Port x mode bits (x = 14)"]
    #[inline(always)]
    pub fn md14(&self) -> Md14R {
        Md14R::new(((self.bits >> 24) & 3) as u8)
    }
    #[doc = "Bits 26:27 - Port x configuration bits (x = 14)"]
    #[inline(always)]
    pub fn ctl14(&self) -> Ctl14R {
        Ctl14R::new(((self.bits >> 26) & 3) as u8)
    }
    #[doc = "Bits 28:29 - Port x mode bits (x = 15)"]
    #[inline(always)]
    pub fn md15(&self) -> Md15R {
        Md15R::new(((self.bits >> 28) & 3) as u8)
    }
    #[doc = "Bits 30:31 - Port x configuration bits (x = 15)"]
    #[inline(always)]
    pub fn ctl15(&self) -> Ctl15R {
        Ctl15R::new(((self.bits >> 30) & 3) as u8)
    }
}
impl W {
    #[doc = "Bits 0:1 - Port x mode bits (x = 8)"]
    #[inline(always)]
    #[must_use]
    pub fn md8(&mut self) -> Md8W<Ctl1Spec> {
        Md8W::new(self, 0)
    }
    #[doc = "Bits 2:3 - Port x configuration bits (x = 8)"]
    #[inline(always)]
    #[must_use]
    pub fn ctl8(&mut self) -> Ctl8W<Ctl1Spec> {
        Ctl8W::new(self, 2)
    }
    #[doc = "Bits 4:5 - Port x mode bits (x = 9)"]
    #[inline(always)]
    #[must_use]
    pub fn md9(&mut self) -> Md9W<Ctl1Spec> {
        Md9W::new(self, 4)
    }
    #[doc = "Bits 6:7 - Port x configuration bits (x = 9)"]
    #[inline(always)]
    #[must_use]
    pub fn ctl9(&mut self) -> Ctl9W<Ctl1Spec> {
        Ctl9W::new(self, 6)
    }
    #[doc = "Bits 8:9 - Port x mode bits (x = 10 )"]
    #[inline(always)]
    #[must_use]
    pub fn md10(&mut self) -> Md10W<Ctl1Spec> {
        Md10W::new(self, 8)
    }
    #[doc = "Bits 10:11 - Port x configuration bits (x = 10)"]
    #[inline(always)]
    #[must_use]
    pub fn ctl10(&mut self) -> Ctl10W<Ctl1Spec> {
        Ctl10W::new(self, 10)
    }
    #[doc = "Bits 12:13 - Port x mode bits (x = 11 )"]
    #[inline(always)]
    #[must_use]
    pub fn md11(&mut self) -> Md11W<Ctl1Spec> {
        Md11W::new(self, 12)
    }
    #[doc = "Bits 14:15 - Port x configuration bits (x = 11)"]
    #[inline(always)]
    #[must_use]
    pub fn ctl11(&mut self) -> Ctl11W<Ctl1Spec> {
        Ctl11W::new(self, 14)
    }
    #[doc = "Bits 16:17 - Port x mode bits (x = 12)"]
    #[inline(always)]
    #[must_use]
    pub fn md12(&mut self) -> Md12W<Ctl1Spec> {
        Md12W::new(self, 16)
    }
    #[doc = "Bits 18:19 - Port x configuration bits (x = 12)"]
    #[inline(always)]
    #[must_use]
    pub fn ctl12(&mut self) -> Ctl12W<Ctl1Spec> {
        Ctl12W::new(self, 18)
    }
    #[doc = "Bits 20:21 - Port x mode bits (x = 13)"]
    #[inline(always)]
    #[must_use]
    pub fn md13(&mut self) -> Md13W<Ctl1Spec> {
        Md13W::new(self, 20)
    }
    #[doc = "Bits 22:23 - Port x configuration bits (x = 13)"]
    #[inline(always)]
    #[must_use]
    pub fn ctl13(&mut self) -> Ctl13W<Ctl1Spec> {
        Ctl13W::new(self, 22)
    }
    #[doc = "Bits 24:25 - Port x mode bits (x = 14)"]
    #[inline(always)]
    #[must_use]
    pub fn md14(&mut self) -> Md14W<Ctl1Spec> {
        Md14W::new(self, 24)
    }
    #[doc = "Bits 26:27 - Port x configuration bits (x = 14)"]
    #[inline(always)]
    #[must_use]
    pub fn ctl14(&mut self) -> Ctl14W<Ctl1Spec> {
        Ctl14W::new(self, 26)
    }
    #[doc = "Bits 28:29 - Port x mode bits (x = 15)"]
    #[inline(always)]
    #[must_use]
    pub fn md15(&mut self) -> Md15W<Ctl1Spec> {
        Md15W::new(self, 28)
    }
    #[doc = "Bits 30:31 - Port x configuration bits (x = 15)"]
    #[inline(always)]
    #[must_use]
    pub fn ctl15(&mut self) -> Ctl15W<Ctl1Spec> {
        Ctl15W::new(self, 30)
    }
}
#[doc = "port control register 1\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`ctl1::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`ctl1::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct Ctl1Spec;
impl crate::RegisterSpec for Ctl1Spec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`ctl1::R`](R) reader structure"]
impl crate::Readable for Ctl1Spec {}
#[doc = "`write(|w| ..)` method takes [`ctl1::W`](W) writer structure"]
impl crate::Writable for Ctl1Spec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets CTL1 to value 0x4444_4444"]
impl crate::Resettable for Ctl1Spec {
    const RESET_VALUE: u32 = 0x4444_4444;
}
