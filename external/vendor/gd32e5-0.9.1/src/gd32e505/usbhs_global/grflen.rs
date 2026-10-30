#[doc = "Register `GRFLEN` reader"]
pub type R = crate::R<GrflenSpec>;
#[doc = "Register `GRFLEN` writer"]
pub type W = crate::W<GrflenSpec>;
#[doc = "Field `RXFD` reader - Rx FIFO depth"]
pub type RxfdR = crate::FieldReader<u16>;
#[doc = "Field `RXFD` writer - Rx FIFO depth"]
pub type RxfdW<'a, REG> = crate::FieldWriter<'a, REG, 16, u16>;
impl R {
    #[doc = "Bits 0:15 - Rx FIFO depth"]
    #[inline(always)]
    pub fn rxfd(&self) -> RxfdR {
        RxfdR::new((self.bits & 0xffff) as u16)
    }
}
impl W {
    #[doc = "Bits 0:15 - Rx FIFO depth"]
    #[inline(always)]
    #[must_use]
    pub fn rxfd(&mut self) -> RxfdW<GrflenSpec> {
        RxfdW::new(self, 0)
    }
}
#[doc = "Global Receive FIFO size register (USBHS_GRFLEN)\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`grflen::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`grflen::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct GrflenSpec;
impl crate::RegisterSpec for GrflenSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`grflen::R`](R) reader structure"]
impl crate::Readable for GrflenSpec {}
#[doc = "`write(|w| ..)` method takes [`grflen::W`](W) writer structure"]
impl crate::Writable for GrflenSpec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets GRFLEN to value 0x0200"]
impl crate::Resettable for GrflenSpec {
    const RESET_VALUE: u32 = 0x0200;
}
