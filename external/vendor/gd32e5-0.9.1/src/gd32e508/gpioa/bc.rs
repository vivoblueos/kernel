#[doc = "Register `BC` writer"]
pub type W = crate::W<BcSpec>;
#[doc = "Port 0 Clear bit\n\nValue on reset: 0"]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Cr0w {
    #[doc = "1: Resets the corresponding OCTLx bit"]
    Reset = 1,
}
impl From<Cr0w> for bool {
    #[inline(always)]
    fn from(variant: Cr0w) -> Self {
        variant as u8 != 0
    }
}
#[doc = "Field `CR0` writer - Port 0 Clear bit"]
pub type Cr0W<'a, REG> = crate::BitWriter<'a, REG, Cr0w>;
impl<'a, REG> Cr0W<'a, REG>
where
    REG: crate::Writable + crate::RegisterSpec,
{
    #[doc = "Resets the corresponding OCTLx bit"]
    #[inline(always)]
    pub fn reset(self) -> &'a mut crate::W<REG> {
        self.variant(Cr0w::Reset)
    }
}
#[doc = "Field `CR1` writer - Port 1 Clear bit"]
pub use Cr0W as Cr1W;
#[doc = "Field `CR2` writer - Port 2 Clear bit"]
pub use Cr0W as Cr2W;
#[doc = "Field `CR3` writer - Port 3 Clear bit"]
pub use Cr0W as Cr3W;
#[doc = "Field `CR4` writer - Port 4 Clear bit"]
pub use Cr0W as Cr4W;
#[doc = "Field `CR5` writer - Port 5 Clear bit"]
pub use Cr0W as Cr5W;
#[doc = "Field `CR6` writer - Port 6 Clear bit"]
pub use Cr0W as Cr6W;
#[doc = "Field `CR7` writer - Port 7 Clear bit"]
pub use Cr0W as Cr7W;
#[doc = "Field `CR8` writer - Port 8 Clear bit"]
pub use Cr0W as Cr8W;
#[doc = "Field `CR9` writer - Port 9 Clear bit"]
pub use Cr0W as Cr9W;
#[doc = "Field `CR10` writer - Port 10 Clear bit"]
pub use Cr0W as Cr10W;
#[doc = "Field `CR11` writer - Port 11 Clear bit"]
pub use Cr0W as Cr11W;
#[doc = "Field `CR12` writer - Port 12 Clear bit"]
pub use Cr0W as Cr12W;
#[doc = "Field `CR13` writer - Port 13 Clear bit"]
pub use Cr0W as Cr13W;
#[doc = "Field `CR14` writer - Port 14 Clear bit"]
pub use Cr0W as Cr14W;
#[doc = "Field `CR15` writer - Port 15 Clear bit"]
pub use Cr0W as Cr15W;
impl W {
    #[doc = "Bit 0 - Port 0 Clear bit"]
    #[inline(always)]
    #[must_use]
    pub fn cr0(&mut self) -> Cr0W<BcSpec> {
        Cr0W::new(self, 0)
    }
    #[doc = "Bit 1 - Port 1 Clear bit"]
    #[inline(always)]
    #[must_use]
    pub fn cr1(&mut self) -> Cr1W<BcSpec> {
        Cr1W::new(self, 1)
    }
    #[doc = "Bit 2 - Port 2 Clear bit"]
    #[inline(always)]
    #[must_use]
    pub fn cr2(&mut self) -> Cr2W<BcSpec> {
        Cr2W::new(self, 2)
    }
    #[doc = "Bit 3 - Port 3 Clear bit"]
    #[inline(always)]
    #[must_use]
    pub fn cr3(&mut self) -> Cr3W<BcSpec> {
        Cr3W::new(self, 3)
    }
    #[doc = "Bit 4 - Port 4 Clear bit"]
    #[inline(always)]
    #[must_use]
    pub fn cr4(&mut self) -> Cr4W<BcSpec> {
        Cr4W::new(self, 4)
    }
    #[doc = "Bit 5 - Port 5 Clear bit"]
    #[inline(always)]
    #[must_use]
    pub fn cr5(&mut self) -> Cr5W<BcSpec> {
        Cr5W::new(self, 5)
    }
    #[doc = "Bit 6 - Port 6 Clear bit"]
    #[inline(always)]
    #[must_use]
    pub fn cr6(&mut self) -> Cr6W<BcSpec> {
        Cr6W::new(self, 6)
    }
    #[doc = "Bit 7 - Port 7 Clear bit"]
    #[inline(always)]
    #[must_use]
    pub fn cr7(&mut self) -> Cr7W<BcSpec> {
        Cr7W::new(self, 7)
    }
    #[doc = "Bit 8 - Port 8 Clear bit"]
    #[inline(always)]
    #[must_use]
    pub fn cr8(&mut self) -> Cr8W<BcSpec> {
        Cr8W::new(self, 8)
    }
    #[doc = "Bit 9 - Port 9 Clear bit"]
    #[inline(always)]
    #[must_use]
    pub fn cr9(&mut self) -> Cr9W<BcSpec> {
        Cr9W::new(self, 9)
    }
    #[doc = "Bit 10 - Port 10 Clear bit"]
    #[inline(always)]
    #[must_use]
    pub fn cr10(&mut self) -> Cr10W<BcSpec> {
        Cr10W::new(self, 10)
    }
    #[doc = "Bit 11 - Port 11 Clear bit"]
    #[inline(always)]
    #[must_use]
    pub fn cr11(&mut self) -> Cr11W<BcSpec> {
        Cr11W::new(self, 11)
    }
    #[doc = "Bit 12 - Port 12 Clear bit"]
    #[inline(always)]
    #[must_use]
    pub fn cr12(&mut self) -> Cr12W<BcSpec> {
        Cr12W::new(self, 12)
    }
    #[doc = "Bit 13 - Port 13 Clear bit"]
    #[inline(always)]
    #[must_use]
    pub fn cr13(&mut self) -> Cr13W<BcSpec> {
        Cr13W::new(self, 13)
    }
    #[doc = "Bit 14 - Port 14 Clear bit"]
    #[inline(always)]
    #[must_use]
    pub fn cr14(&mut self) -> Cr14W<BcSpec> {
        Cr14W::new(self, 14)
    }
    #[doc = "Bit 15 - Port 15 Clear bit"]
    #[inline(always)]
    #[must_use]
    pub fn cr15(&mut self) -> Cr15W<BcSpec> {
        Cr15W::new(self, 15)
    }
}
#[doc = "Port bit clear register\n\nYou can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`bc::W`](W). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct BcSpec;
impl crate::RegisterSpec for BcSpec {
    type Ux = u32;
}
#[doc = "`write(|w| ..)` method takes [`bc::W`](W) writer structure"]
impl crate::Writable for BcSpec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets BC to value 0"]
impl crate::Resettable for BcSpec {
    const RESET_VALUE: u32 = 0;
}
