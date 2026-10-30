#[doc = "Register `INTF` reader"]
pub type R = crate::R<IntfSpec>;
#[doc = "Global interrupt flag of channel 0\n\nValue on reset: 0"]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Gif0 {
    #[doc = "0: No transfer error, half event, complete event"]
    NoEvent = 0,
    #[doc = "1: A transfer error, half event or complete event has occured"]
    Event = 1,
}
impl From<Gif0> for bool {
    #[inline(always)]
    fn from(variant: Gif0) -> Self {
        variant as u8 != 0
    }
}
#[doc = "Field `GIF0` reader - Global interrupt flag of channel 0"]
pub type Gif0R = crate::BitReader<Gif0>;
impl Gif0R {
    #[doc = "Get enumerated values variant"]
    #[inline(always)]
    pub const fn variant(&self) -> Gif0 {
        match self.bits {
            false => Gif0::NoEvent,
            true => Gif0::Event,
        }
    }
    #[doc = "No transfer error, half event, complete event"]
    #[inline(always)]
    pub fn is_no_event(&self) -> bool {
        *self == Gif0::NoEvent
    }
    #[doc = "A transfer error, half event or complete event has occured"]
    #[inline(always)]
    pub fn is_event(&self) -> bool {
        *self == Gif0::Event
    }
}
#[doc = "Full Transfer finish flag of channe 0\n\nValue on reset: 0"]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Ftfif0 {
    #[doc = "0: No transfer complete event"]
    NotComplete = 0,
    #[doc = "1: A transfer complete event has occured"]
    Complete = 1,
}
impl From<Ftfif0> for bool {
    #[inline(always)]
    fn from(variant: Ftfif0) -> Self {
        variant as u8 != 0
    }
}
#[doc = "Field `FTFIF0` reader - Full Transfer finish flag of channe 0"]
pub type Ftfif0R = crate::BitReader<Ftfif0>;
impl Ftfif0R {
    #[doc = "Get enumerated values variant"]
    #[inline(always)]
    pub const fn variant(&self) -> Ftfif0 {
        match self.bits {
            false => Ftfif0::NotComplete,
            true => Ftfif0::Complete,
        }
    }
    #[doc = "No transfer complete event"]
    #[inline(always)]
    pub fn is_not_complete(&self) -> bool {
        *self == Ftfif0::NotComplete
    }
    #[doc = "A transfer complete event has occured"]
    #[inline(always)]
    pub fn is_complete(&self) -> bool {
        *self == Ftfif0::Complete
    }
}
#[doc = "Half transfer finish flag of channel 0\n\nValue on reset: 0"]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Htfif0 {
    #[doc = "0: No half transfer event"]
    NotHalf = 0,
    #[doc = "1: A half transfer event has occured"]
    Half = 1,
}
impl From<Htfif0> for bool {
    #[inline(always)]
    fn from(variant: Htfif0) -> Self {
        variant as u8 != 0
    }
}
#[doc = "Field `HTFIF0` reader - Half transfer finish flag of channel 0"]
pub type Htfif0R = crate::BitReader<Htfif0>;
impl Htfif0R {
    #[doc = "Get enumerated values variant"]
    #[inline(always)]
    pub const fn variant(&self) -> Htfif0 {
        match self.bits {
            false => Htfif0::NotHalf,
            true => Htfif0::Half,
        }
    }
    #[doc = "No half transfer event"]
    #[inline(always)]
    pub fn is_not_half(&self) -> bool {
        *self == Htfif0::NotHalf
    }
    #[doc = "A half transfer event has occured"]
    #[inline(always)]
    pub fn is_half(&self) -> bool {
        *self == Htfif0::Half
    }
}
#[doc = "Error flag of channel 0\n\nValue on reset: 0"]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Errif0 {
    #[doc = "0: No transfer error"]
    NoError = 0,
    #[doc = "1: A transfer error has occured"]
    Error = 1,
}
impl From<Errif0> for bool {
    #[inline(always)]
    fn from(variant: Errif0) -> Self {
        variant as u8 != 0
    }
}
#[doc = "Field `ERRIF0` reader - Error flag of channel 0"]
pub type Errif0R = crate::BitReader<Errif0>;
impl Errif0R {
    #[doc = "Get enumerated values variant"]
    #[inline(always)]
    pub const fn variant(&self) -> Errif0 {
        match self.bits {
            false => Errif0::NoError,
            true => Errif0::Error,
        }
    }
    #[doc = "No transfer error"]
    #[inline(always)]
    pub fn is_no_error(&self) -> bool {
        *self == Errif0::NoError
    }
    #[doc = "A transfer error has occured"]
    #[inline(always)]
    pub fn is_error(&self) -> bool {
        *self == Errif0::Error
    }
}
#[doc = "Field `ERRIF1` reader - Error flag of channel 1"]
pub use Errif0R as Errif1R;
#[doc = "Field `ERRIF2` reader - Error flag of channel 2"]
pub use Errif0R as Errif2R;
#[doc = "Field `ERRIF3` reader - Error flag of channel 3"]
pub use Errif0R as Errif3R;
#[doc = "Field `ERRIF4` reader - Error flag of channel 4"]
pub use Errif0R as Errif4R;
#[doc = "Field `ERRIF5` reader - Error flag of channel 5"]
pub use Errif0R as Errif5R;
#[doc = "Field `ERRIF6` reader - Error flag of channel 6"]
pub use Errif0R as Errif6R;
#[doc = "Field `FTFIF1` reader - Full Transfer finish flag of channe 1"]
pub use Ftfif0R as Ftfif1R;
#[doc = "Field `FTFIF2` reader - Full Transfer finish flag of channe 2"]
pub use Ftfif0R as Ftfif2R;
#[doc = "Field `FTFIF3` reader - Full Transfer finish flag of channe 3"]
pub use Ftfif0R as Ftfif3R;
#[doc = "Field `FTFIF4` reader - Full Transfer finish flag of channe 4"]
pub use Ftfif0R as Ftfif4R;
#[doc = "Field `FTFIF5` reader - Full Transfer finish flag of channe 5"]
pub use Ftfif0R as Ftfif5R;
#[doc = "Field `FTFIF6` reader - Full Transfer finish flag of channe 6"]
pub use Ftfif0R as Ftfif6R;
#[doc = "Field `GIF1` reader - Global interrupt flag of channel 1"]
pub use Gif0R as Gif1R;
#[doc = "Field `GIF2` reader - Global interrupt flag of channel 2"]
pub use Gif0R as Gif2R;
#[doc = "Field `GIF3` reader - Global interrupt flag of channel 3"]
pub use Gif0R as Gif3R;
#[doc = "Field `GIF4` reader - Global interrupt flag of channel 4"]
pub use Gif0R as Gif4R;
#[doc = "Field `GIF5` reader - Global interrupt flag of channel 5"]
pub use Gif0R as Gif5R;
#[doc = "Field `GIF6` reader - Global interrupt flag of channel 6"]
pub use Gif0R as Gif6R;
#[doc = "Field `HTFIF1` reader - Half transfer finish flag of channel 1"]
pub use Htfif0R as Htfif1R;
#[doc = "Field `HTFIF2` reader - Half transfer finish flag of channel 2"]
pub use Htfif0R as Htfif2R;
#[doc = "Field `HTFIF3` reader - Half transfer finish flag of channel 3"]
pub use Htfif0R as Htfif3R;
#[doc = "Field `HTFIF4` reader - Half transfer finish flag of channel 4"]
pub use Htfif0R as Htfif4R;
#[doc = "Field `HTFIF5` reader - Half transfer finish flag of channel 5"]
pub use Htfif0R as Htfif5R;
#[doc = "Field `HTFIF6` reader - Half transfer finish flag of channel 6"]
pub use Htfif0R as Htfif6R;
impl R {
    #[doc = "Bit 0 - Global interrupt flag of channel 0"]
    #[inline(always)]
    pub fn gif0(&self) -> Gif0R {
        Gif0R::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - Full Transfer finish flag of channe 0"]
    #[inline(always)]
    pub fn ftfif0(&self) -> Ftfif0R {
        Ftfif0R::new(((self.bits >> 1) & 1) != 0)
    }
    #[doc = "Bit 2 - Half transfer finish flag of channel 0"]
    #[inline(always)]
    pub fn htfif0(&self) -> Htfif0R {
        Htfif0R::new(((self.bits >> 2) & 1) != 0)
    }
    #[doc = "Bit 3 - Error flag of channel 0"]
    #[inline(always)]
    pub fn errif0(&self) -> Errif0R {
        Errif0R::new(((self.bits >> 3) & 1) != 0)
    }
    #[doc = "Bit 4 - Global interrupt flag of channel 1"]
    #[inline(always)]
    pub fn gif1(&self) -> Gif1R {
        Gif1R::new(((self.bits >> 4) & 1) != 0)
    }
    #[doc = "Bit 5 - Full Transfer finish flag of channe 1"]
    #[inline(always)]
    pub fn ftfif1(&self) -> Ftfif1R {
        Ftfif1R::new(((self.bits >> 5) & 1) != 0)
    }
    #[doc = "Bit 6 - Half transfer finish flag of channel 1"]
    #[inline(always)]
    pub fn htfif1(&self) -> Htfif1R {
        Htfif1R::new(((self.bits >> 6) & 1) != 0)
    }
    #[doc = "Bit 7 - Error flag of channel 1"]
    #[inline(always)]
    pub fn errif1(&self) -> Errif1R {
        Errif1R::new(((self.bits >> 7) & 1) != 0)
    }
    #[doc = "Bit 8 - Global interrupt flag of channel 2"]
    #[inline(always)]
    pub fn gif2(&self) -> Gif2R {
        Gif2R::new(((self.bits >> 8) & 1) != 0)
    }
    #[doc = "Bit 9 - Full Transfer finish flag of channe 2"]
    #[inline(always)]
    pub fn ftfif2(&self) -> Ftfif2R {
        Ftfif2R::new(((self.bits >> 9) & 1) != 0)
    }
    #[doc = "Bit 10 - Half transfer finish flag of channel 2"]
    #[inline(always)]
    pub fn htfif2(&self) -> Htfif2R {
        Htfif2R::new(((self.bits >> 10) & 1) != 0)
    }
    #[doc = "Bit 11 - Error flag of channel 2"]
    #[inline(always)]
    pub fn errif2(&self) -> Errif2R {
        Errif2R::new(((self.bits >> 11) & 1) != 0)
    }
    #[doc = "Bit 12 - Global interrupt flag of channel 3"]
    #[inline(always)]
    pub fn gif3(&self) -> Gif3R {
        Gif3R::new(((self.bits >> 12) & 1) != 0)
    }
    #[doc = "Bit 13 - Full Transfer finish flag of channe 3"]
    #[inline(always)]
    pub fn ftfif3(&self) -> Ftfif3R {
        Ftfif3R::new(((self.bits >> 13) & 1) != 0)
    }
    #[doc = "Bit 14 - Half transfer finish flag of channel 3"]
    #[inline(always)]
    pub fn htfif3(&self) -> Htfif3R {
        Htfif3R::new(((self.bits >> 14) & 1) != 0)
    }
    #[doc = "Bit 15 - Error flag of channel 3"]
    #[inline(always)]
    pub fn errif3(&self) -> Errif3R {
        Errif3R::new(((self.bits >> 15) & 1) != 0)
    }
    #[doc = "Bit 16 - Global interrupt flag of channel 4"]
    #[inline(always)]
    pub fn gif4(&self) -> Gif4R {
        Gif4R::new(((self.bits >> 16) & 1) != 0)
    }
    #[doc = "Bit 17 - Full Transfer finish flag of channe 4"]
    #[inline(always)]
    pub fn ftfif4(&self) -> Ftfif4R {
        Ftfif4R::new(((self.bits >> 17) & 1) != 0)
    }
    #[doc = "Bit 18 - Half transfer finish flag of channel 4"]
    #[inline(always)]
    pub fn htfif4(&self) -> Htfif4R {
        Htfif4R::new(((self.bits >> 18) & 1) != 0)
    }
    #[doc = "Bit 19 - Error flag of channel 4"]
    #[inline(always)]
    pub fn errif4(&self) -> Errif4R {
        Errif4R::new(((self.bits >> 19) & 1) != 0)
    }
    #[doc = "Bit 20 - Global interrupt flag of channel 5"]
    #[inline(always)]
    pub fn gif5(&self) -> Gif5R {
        Gif5R::new(((self.bits >> 20) & 1) != 0)
    }
    #[doc = "Bit 21 - Full Transfer finish flag of channe 5"]
    #[inline(always)]
    pub fn ftfif5(&self) -> Ftfif5R {
        Ftfif5R::new(((self.bits >> 21) & 1) != 0)
    }
    #[doc = "Bit 22 - Half transfer finish flag of channel 5"]
    #[inline(always)]
    pub fn htfif5(&self) -> Htfif5R {
        Htfif5R::new(((self.bits >> 22) & 1) != 0)
    }
    #[doc = "Bit 23 - Error flag of channel 5"]
    #[inline(always)]
    pub fn errif5(&self) -> Errif5R {
        Errif5R::new(((self.bits >> 23) & 1) != 0)
    }
    #[doc = "Bit 24 - Global interrupt flag of channel 6"]
    #[inline(always)]
    pub fn gif6(&self) -> Gif6R {
        Gif6R::new(((self.bits >> 24) & 1) != 0)
    }
    #[doc = "Bit 25 - Full Transfer finish flag of channe 6"]
    #[inline(always)]
    pub fn ftfif6(&self) -> Ftfif6R {
        Ftfif6R::new(((self.bits >> 25) & 1) != 0)
    }
    #[doc = "Bit 26 - Half transfer finish flag of channel 6"]
    #[inline(always)]
    pub fn htfif6(&self) -> Htfif6R {
        Htfif6R::new(((self.bits >> 26) & 1) != 0)
    }
    #[doc = "Bit 27 - Error flag of channel 6"]
    #[inline(always)]
    pub fn errif6(&self) -> Errif6R {
        Errif6R::new(((self.bits >> 27) & 1) != 0)
    }
}
#[doc = "Interrupt flag register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`intf::R`](R).  See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct IntfSpec;
impl crate::RegisterSpec for IntfSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`intf::R`](R) reader structure"]
impl crate::Readable for IntfSpec {}
#[doc = "`reset()` method sets INTF to value 0"]
impl crate::Resettable for IntfSpec {
    const RESET_VALUE: u32 = 0;
}
