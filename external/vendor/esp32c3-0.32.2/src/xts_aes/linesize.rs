#[doc = "Register `LINESIZE` reader"]
pub type R = crate::R<LINESIZE_SPEC>;
#[doc = "Register `LINESIZE` writer"]
pub type W = crate::W<LINESIZE_SPEC>;
#[doc = "Field `LINESIZE` reader - This bit stores the line size parameter. 0: 16Byte, 1: 32Byte."]
pub type LINESIZE_R = crate::BitReader;
#[doc = "Field `LINESIZE` writer - This bit stores the line size parameter. 0: 16Byte, 1: 32Byte."]
pub type LINESIZE_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 0 - This bit stores the line size parameter. 0: 16Byte, 1: 32Byte."]
    #[inline(always)]
    pub fn linesize(&self) -> LINESIZE_R {
        LINESIZE_R::new((self.bits & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("LINESIZE")
            .field("linesize", &self.linesize())
            .finish()
    }
}
impl W {
    #[doc = "Bit 0 - This bit stores the line size parameter. 0: 16Byte, 1: 32Byte."]
    #[inline(always)]
    pub fn linesize(&mut self) -> LINESIZE_W<'_, LINESIZE_SPEC> {
        LINESIZE_W::new(self, 0)
    }
}
#[doc = "XTS-AES line-size register\n\nYou can [`read`](crate::Reg::read) this register and get [`linesize::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`linesize::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct LINESIZE_SPEC;
impl crate::RegisterSpec for LINESIZE_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`linesize::R`](R) reader structure"]
impl crate::Readable for LINESIZE_SPEC {}
#[doc = "`write(|w| ..)` method takes [`linesize::W`](W) writer structure"]
impl crate::Writable for LINESIZE_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets LINESIZE to value 0"]
impl crate::Resettable for LINESIZE_SPEC {}
