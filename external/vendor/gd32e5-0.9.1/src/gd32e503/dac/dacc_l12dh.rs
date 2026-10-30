#[doc = "Register `DACC_L12DH` reader"]
pub type R = crate::R<DaccL12dhSpec>;
#[doc = "Register `DACC_L12DH` writer"]
pub type W = crate::W<DaccL12dhSpec>;
#[doc = "Field `OUT0_DH` reader - DAC_OUT0 12-bit left-aligned data"]
pub type Out0DhR = crate::FieldReader<u16>;
#[doc = "Field `OUT0_DH` writer - DAC_OUT0 12-bit left-aligned data"]
pub type Out0DhW<'a, REG> = crate::FieldWriter<'a, REG, 12, u16>;
#[doc = "Field `OUT1_DH` reader - DAC_OUT1 12-bit left-aligned data"]
pub type Out1DhR = crate::FieldReader<u16>;
#[doc = "Field `OUT1_DH` writer - DAC_OUT1 12-bit left-aligned data"]
pub type Out1DhW<'a, REG> = crate::FieldWriter<'a, REG, 12, u16>;
impl R {
    #[doc = "Bits 4:15 - DAC_OUT0 12-bit left-aligned data"]
    #[inline(always)]
    pub fn out0_dh(&self) -> Out0DhR {
        Out0DhR::new(((self.bits >> 4) & 0x0fff) as u16)
    }
    #[doc = "Bits 20:31 - DAC_OUT1 12-bit left-aligned data"]
    #[inline(always)]
    pub fn out1_dh(&self) -> Out1DhR {
        Out1DhR::new(((self.bits >> 20) & 0x0fff) as u16)
    }
}
impl W {
    #[doc = "Bits 4:15 - DAC_OUT0 12-bit left-aligned data"]
    #[inline(always)]
    #[must_use]
    pub fn out0_dh(&mut self) -> Out0DhW<DaccL12dhSpec> {
        Out0DhW::new(self, 4)
    }
    #[doc = "Bits 20:31 - DAC_OUT1 12-bit left-aligned data"]
    #[inline(always)]
    #[must_use]
    pub fn out1_dh(&mut self) -> Out1DhW<DaccL12dhSpec> {
        Out1DhW::new(self, 20)
    }
}
#[doc = "DAC concurrent mode 12-bit left aligned data holding register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`dacc_l12dh::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`dacc_l12dh::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct DaccL12dhSpec;
impl crate::RegisterSpec for DaccL12dhSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`dacc_l12dh::R`](R) reader structure"]
impl crate::Readable for DaccL12dhSpec {}
#[doc = "`write(|w| ..)` method takes [`dacc_l12dh::W`](W) writer structure"]
impl crate::Writable for DaccL12dhSpec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets DACC_L12DH to value 0"]
impl crate::Resettable for DaccL12dhSpec {
    const RESET_VALUE: u32 = 0;
}
