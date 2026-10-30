#[doc = "Register `ISTAT` reader"]
pub type R = crate::R<IstatSpec>;
#[doc = "Port input status\n\nValue on reset: 0"]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Istat0 {
    #[doc = "0: Input is logic low"]
    Low = 0,
    #[doc = "1: Input is logic high"]
    High = 1,
}
impl From<Istat0> for bool {
    #[inline(always)]
    fn from(variant: Istat0) -> Self {
        variant as u8 != 0
    }
}
#[doc = "Field `ISTAT0` reader - Port input status"]
pub type Istat0R = crate::BitReader<Istat0>;
impl Istat0R {
    #[doc = "Get enumerated values variant"]
    #[inline(always)]
    pub const fn variant(&self) -> Istat0 {
        match self.bits {
            false => Istat0::Low,
            true => Istat0::High,
        }
    }
    #[doc = "Input is logic low"]
    #[inline(always)]
    pub fn is_low(&self) -> bool {
        *self == Istat0::Low
    }
    #[doc = "Input is logic high"]
    #[inline(always)]
    pub fn is_high(&self) -> bool {
        *self == Istat0::High
    }
}
#[doc = "Field `ISTAT1` reader - Port input status"]
pub use Istat0R as Istat1R;
#[doc = "Field `ISTAT2` reader - Port input status"]
pub use Istat0R as Istat2R;
#[doc = "Field `ISTAT3` reader - Port input status"]
pub use Istat0R as Istat3R;
#[doc = "Field `ISTAT4` reader - Port input status"]
pub use Istat0R as Istat4R;
#[doc = "Field `ISTAT5` reader - Port input status"]
pub use Istat0R as Istat5R;
#[doc = "Field `ISTAT6` reader - Port input status"]
pub use Istat0R as Istat6R;
#[doc = "Field `ISTAT7` reader - Port input status"]
pub use Istat0R as Istat7R;
#[doc = "Field `ISTAT8` reader - Port input status"]
pub use Istat0R as Istat8R;
#[doc = "Field `ISTAT9` reader - Port input status"]
pub use Istat0R as Istat9R;
#[doc = "Field `ISTAT10` reader - Port input status"]
pub use Istat0R as Istat10R;
#[doc = "Field `ISTAT11` reader - Port input status"]
pub use Istat0R as Istat11R;
#[doc = "Field `ISTAT12` reader - Port input status"]
pub use Istat0R as Istat12R;
#[doc = "Field `ISTAT13` reader - Port input status"]
pub use Istat0R as Istat13R;
#[doc = "Field `ISTAT14` reader - Port input status"]
pub use Istat0R as Istat14R;
#[doc = "Field `ISTAT15` reader - Port input status"]
pub use Istat0R as Istat15R;
impl R {
    #[doc = "Bit 0 - Port input status"]
    #[inline(always)]
    pub fn istat0(&self) -> Istat0R {
        Istat0R::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - Port input status"]
    #[inline(always)]
    pub fn istat1(&self) -> Istat1R {
        Istat1R::new(((self.bits >> 1) & 1) != 0)
    }
    #[doc = "Bit 2 - Port input status"]
    #[inline(always)]
    pub fn istat2(&self) -> Istat2R {
        Istat2R::new(((self.bits >> 2) & 1) != 0)
    }
    #[doc = "Bit 3 - Port input status"]
    #[inline(always)]
    pub fn istat3(&self) -> Istat3R {
        Istat3R::new(((self.bits >> 3) & 1) != 0)
    }
    #[doc = "Bit 4 - Port input status"]
    #[inline(always)]
    pub fn istat4(&self) -> Istat4R {
        Istat4R::new(((self.bits >> 4) & 1) != 0)
    }
    #[doc = "Bit 5 - Port input status"]
    #[inline(always)]
    pub fn istat5(&self) -> Istat5R {
        Istat5R::new(((self.bits >> 5) & 1) != 0)
    }
    #[doc = "Bit 6 - Port input status"]
    #[inline(always)]
    pub fn istat6(&self) -> Istat6R {
        Istat6R::new(((self.bits >> 6) & 1) != 0)
    }
    #[doc = "Bit 7 - Port input status"]
    #[inline(always)]
    pub fn istat7(&self) -> Istat7R {
        Istat7R::new(((self.bits >> 7) & 1) != 0)
    }
    #[doc = "Bit 8 - Port input status"]
    #[inline(always)]
    pub fn istat8(&self) -> Istat8R {
        Istat8R::new(((self.bits >> 8) & 1) != 0)
    }
    #[doc = "Bit 9 - Port input status"]
    #[inline(always)]
    pub fn istat9(&self) -> Istat9R {
        Istat9R::new(((self.bits >> 9) & 1) != 0)
    }
    #[doc = "Bit 10 - Port input status"]
    #[inline(always)]
    pub fn istat10(&self) -> Istat10R {
        Istat10R::new(((self.bits >> 10) & 1) != 0)
    }
    #[doc = "Bit 11 - Port input status"]
    #[inline(always)]
    pub fn istat11(&self) -> Istat11R {
        Istat11R::new(((self.bits >> 11) & 1) != 0)
    }
    #[doc = "Bit 12 - Port input status"]
    #[inline(always)]
    pub fn istat12(&self) -> Istat12R {
        Istat12R::new(((self.bits >> 12) & 1) != 0)
    }
    #[doc = "Bit 13 - Port input status"]
    #[inline(always)]
    pub fn istat13(&self) -> Istat13R {
        Istat13R::new(((self.bits >> 13) & 1) != 0)
    }
    #[doc = "Bit 14 - Port input status"]
    #[inline(always)]
    pub fn istat14(&self) -> Istat14R {
        Istat14R::new(((self.bits >> 14) & 1) != 0)
    }
    #[doc = "Bit 15 - Port input status"]
    #[inline(always)]
    pub fn istat15(&self) -> Istat15R {
        Istat15R::new(((self.bits >> 15) & 1) != 0)
    }
}
#[doc = "Port input status register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`istat::R`](R).  See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct IstatSpec;
impl crate::RegisterSpec for IstatSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`istat::R`](R) reader structure"]
impl crate::Readable for IstatSpec {}
#[doc = "`reset()` method sets ISTAT to value 0"]
impl crate::Resettable for IstatSpec {
    const RESET_VALUE: u32 = 0;
}
