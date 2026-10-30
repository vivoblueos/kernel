#[doc = "Register `DIFCTL` reader"]
pub type R = crate::R<DifctlSpec>;
#[doc = "Register `DIFCTL` writer"]
pub type W = crate::W<DifctlSpec>;
#[doc = "Field `DIFCTL_14_0` reader - Differential mode for channel 14 to 0"]
pub type Difctl14_0R = crate::FieldReader<u16>;
#[doc = "Field `DIFCTL_14_0` writer - Differential mode for channel 14 to 0"]
pub type Difctl14_0W<'a, REG> = crate::FieldWriter<'a, REG, 15, u16>;
#[doc = "Field `DIFCTL_17_15` reader - Differential mode for channel 17 to 15"]
pub type Difctl17_15R = crate::FieldReader;
impl R {
    #[doc = "Bits 0:14 - Differential mode for channel 14 to 0"]
    #[inline(always)]
    pub fn difctl_14_0(&self) -> Difctl14_0R {
        Difctl14_0R::new((self.bits & 0x7fff) as u16)
    }
    #[doc = "Bits 15:17 - Differential mode for channel 17 to 15"]
    #[inline(always)]
    pub fn difctl_17_15(&self) -> Difctl17_15R {
        Difctl17_15R::new(((self.bits >> 15) & 7) as u8)
    }
}
impl W {
    #[doc = "Bits 0:14 - Differential mode for channel 14 to 0"]
    #[inline(always)]
    #[must_use]
    pub fn difctl_14_0(&mut self) -> Difctl14_0W<DifctlSpec> {
        Difctl14_0W::new(self, 0)
    }
}
#[doc = "Differential mode control register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`difctl::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`difctl::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct DifctlSpec;
impl crate::RegisterSpec for DifctlSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`difctl::R`](R) reader structure"]
impl crate::Readable for DifctlSpec {}
#[doc = "`write(|w| ..)` method takes [`difctl::W`](W) writer structure"]
impl crate::Writable for DifctlSpec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets DIFCTL to value 0"]
impl crate::Resettable for DifctlSpec {
    const RESET_VALUE: u32 = 0;
}
