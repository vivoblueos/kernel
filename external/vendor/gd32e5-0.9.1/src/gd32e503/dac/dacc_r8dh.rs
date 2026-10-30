#[doc = "Register `DACC_R8DH` reader"]
pub type R = crate::R<DaccR8dhSpec>;
#[doc = "Register `DACC_R8DH` writer"]
pub type W = crate::W<DaccR8dhSpec>;
#[doc = "Field `OUT0_DH` reader - DAC_OUT0 8-bit right-aligned data"]
pub type Out0DhR = crate::FieldReader;
#[doc = "Field `OUT0_DH` writer - DAC_OUT0 8-bit right-aligned data"]
pub type Out0DhW<'a, REG> = crate::FieldWriter<'a, REG, 8>;
#[doc = "Field `OUT1_DH` reader - DAC_OUT1 8-bit right-aligned data"]
pub type Out1DhR = crate::FieldReader;
#[doc = "Field `OUT1_DH` writer - DAC_OUT1 8-bit right-aligned data"]
pub type Out1DhW<'a, REG> = crate::FieldWriter<'a, REG, 8>;
impl R {
    #[doc = "Bits 0:7 - DAC_OUT0 8-bit right-aligned data"]
    #[inline(always)]
    pub fn out0_dh(&self) -> Out0DhR {
        Out0DhR::new((self.bits & 0xff) as u8)
    }
    #[doc = "Bits 8:15 - DAC_OUT1 8-bit right-aligned data"]
    #[inline(always)]
    pub fn out1_dh(&self) -> Out1DhR {
        Out1DhR::new(((self.bits >> 8) & 0xff) as u8)
    }
}
impl W {
    #[doc = "Bits 0:7 - DAC_OUT0 8-bit right-aligned data"]
    #[inline(always)]
    #[must_use]
    pub fn out0_dh(&mut self) -> Out0DhW<DaccR8dhSpec> {
        Out0DhW::new(self, 0)
    }
    #[doc = "Bits 8:15 - DAC_OUT1 8-bit right-aligned data"]
    #[inline(always)]
    #[must_use]
    pub fn out1_dh(&mut self) -> Out1DhW<DaccR8dhSpec> {
        Out1DhW::new(self, 8)
    }
}
#[doc = "DAC concurrent mode 8-bit right aligned data holding register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`dacc_r8dh::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`dacc_r8dh::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct DaccR8dhSpec;
impl crate::RegisterSpec for DaccR8dhSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`dacc_r8dh::R`](R) reader structure"]
impl crate::Readable for DaccR8dhSpec {}
#[doc = "`write(|w| ..)` method takes [`dacc_r8dh::W`](W) writer structure"]
impl crate::Writable for DaccR8dhSpec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets DACC_R8DH to value 0"]
impl crate::Resettable for DaccR8dhSpec {
    const RESET_VALUE: u32 = 0;
}
