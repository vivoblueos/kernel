#[doc = "Register `PCFD` reader"]
pub type R = crate::R<PcfdSpec>;
#[doc = "Register `PCFD` writer"]
pub type W = crate::W<PcfdSpec>;
#[doc = "Field `PD4_AFCFG` reader - PD4 AF function configuration bitse"]
pub type Pd4AfcfgR = crate::BitReader;
#[doc = "Field `PD4_AFCFG` writer - PD4 AF function configuration bitse"]
pub type Pd4AfcfgW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `PD5_AFCFG` reader - PD5 AF function configuration bitse"]
pub type Pd5AfcfgR = crate::BitReader;
#[doc = "Field `PD5_AFCFG` writer - PD5 AF function configuration bitse"]
pub type Pd5AfcfgW<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 8 - PD4 AF function configuration bitse"]
    #[inline(always)]
    pub fn pd4_afcfg(&self) -> Pd4AfcfgR {
        Pd4AfcfgR::new(((self.bits >> 8) & 1) != 0)
    }
    #[doc = "Bit 10 - PD5 AF function configuration bitse"]
    #[inline(always)]
    pub fn pd5_afcfg(&self) -> Pd5AfcfgR {
        Pd5AfcfgR::new(((self.bits >> 10) & 1) != 0)
    }
}
impl W {
    #[doc = "Bit 8 - PD4 AF function configuration bitse"]
    #[inline(always)]
    #[must_use]
    pub fn pd4_afcfg(&mut self) -> Pd4AfcfgW<PcfdSpec> {
        Pd4AfcfgW::new(self, 8)
    }
    #[doc = "Bit 10 - PD5 AF function configuration bitse"]
    #[inline(always)]
    #[must_use]
    pub fn pd5_afcfg(&mut self) -> Pd5AfcfgW<PcfdSpec> {
        Pd5AfcfgW::new(self, 10)
    }
}
#[doc = "AFIO port configuration register D\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`pcfd::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`pcfd::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct PcfdSpec;
impl crate::RegisterSpec for PcfdSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`pcfd::R`](R) reader structure"]
impl crate::Readable for PcfdSpec {}
#[doc = "`write(|w| ..)` method takes [`pcfd::W`](W) writer structure"]
impl crate::Writable for PcfdSpec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets PCFD to value 0"]
impl crate::Resettable for PcfdSpec {
    const RESET_VALUE: u32 = 0;
}
