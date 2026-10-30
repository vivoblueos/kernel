#[doc = "Register `OUT0_R8DH` reader"]
pub type R = crate::R<Out0R8dhSpec>;
#[doc = "Register `OUT0_R8DH` writer"]
pub type W = crate::W<Out0R8dhSpec>;
#[doc = "Field `OUT0_DH` reader - DAC_OUT0 8-bit right-aligned data"]
pub type Out0DhR = crate::FieldReader;
#[doc = "Field `OUT0_DH` writer - DAC_OUT0 8-bit right-aligned data"]
pub type Out0DhW<'a, REG> = crate::FieldWriter<'a, REG, 8>;
impl R {
    #[doc = "Bits 0:7 - DAC_OUT0 8-bit right-aligned data"]
    #[inline(always)]
    pub fn out0_dh(&self) -> Out0DhR {
        Out0DhR::new((self.bits & 0xff) as u8)
    }
}
impl W {
    #[doc = "Bits 0:7 - DAC_OUT0 8-bit right-aligned data"]
    #[inline(always)]
    #[must_use]
    pub fn out0_dh(&mut self) -> Out0DhW<Out0R8dhSpec> {
        Out0DhW::new(self, 0)
    }
}
#[doc = "DAC_OUT0 8-bit right aligned data holding register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`out0_r8dh::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`out0_r8dh::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct Out0R8dhSpec;
impl crate::RegisterSpec for Out0R8dhSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`out0_r8dh::R`](R) reader structure"]
impl crate::Readable for Out0R8dhSpec {}
#[doc = "`write(|w| ..)` method takes [`out0_r8dh::W`](W) writer structure"]
impl crate::Writable for Out0R8dhSpec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets OUT0_R8DH to value 0"]
impl crate::Resettable for Out0R8dhSpec {
    const RESET_VALUE: u32 = 0;
}
