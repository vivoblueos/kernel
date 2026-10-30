#[doc = "Register `ENDIAN` reader"]
pub type R = crate::R<ENDIAN_SPEC>;
#[doc = "Register `ENDIAN` writer"]
pub type W = crate::W<ENDIAN_SPEC>;
#[doc = "Field `ENDIAN` reader - endian. \\[1:0\\] key endian, \\[3:2\\] text_in endian or in_stream endian, \\[5:4\\] text_out endian or out_stream endian"]
pub type ENDIAN_R = crate::FieldReader;
#[doc = "Field `ENDIAN` writer - endian. \\[1:0\\] key endian, \\[3:2\\] text_in endian or in_stream endian, \\[5:4\\] text_out endian or out_stream endian"]
pub type ENDIAN_W<'a, REG> = crate::FieldWriter<'a, REG, 6>;
impl R {
    #[doc = "Bits 0:5 - endian. \\[1:0\\] key endian, \\[3:2\\] text_in endian or in_stream endian, \\[5:4\\] text_out endian or out_stream endian"]
    #[inline(always)]
    pub fn endian(&self) -> ENDIAN_R {
        ENDIAN_R::new((self.bits & 0x3f) as u8)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("ENDIAN")
            .field("endian", &self.endian())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:5 - endian. \\[1:0\\] key endian, \\[3:2\\] text_in endian or in_stream endian, \\[5:4\\] text_out endian or out_stream endian"]
    #[inline(always)]
    pub fn endian(&mut self) -> ENDIAN_W<'_, ENDIAN_SPEC> {
        ENDIAN_W::new(self, 0)
    }
}
#[doc = "AES Endian configure register\n\nYou can [`read`](crate::Reg::read) this register and get [`endian::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`endian::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct ENDIAN_SPEC;
impl crate::RegisterSpec for ENDIAN_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`endian::R`](R) reader structure"]
impl crate::Readable for ENDIAN_SPEC {}
#[doc = "`write(|w| ..)` method takes [`endian::W`](W) writer structure"]
impl crate::Writable for ENDIAN_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets ENDIAN to value 0"]
impl crate::Resettable for ENDIAN_SPEC {}
