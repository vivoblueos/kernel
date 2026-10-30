#[doc = "Register `GET_LINE_CODE_W1` reader"]
pub type R = crate::R<GET_LINE_CODE_W1_SPEC>;
#[doc = "Register `GET_LINE_CODE_W1` writer"]
pub type W = crate::W<GET_LINE_CODE_W1_SPEC>;
#[doc = "Field `GET_BDATA_BITS` reader - The value of bCharFormat set by software which is requested by GET_LINE_CODING command."]
pub type GET_BDATA_BITS_R = crate::FieldReader;
#[doc = "Field `GET_BDATA_BITS` writer - The value of bCharFormat set by software which is requested by GET_LINE_CODING command."]
pub type GET_BDATA_BITS_W<'a, REG> = crate::FieldWriter<'a, REG, 8>;
#[doc = "Field `GET_BPARITY_TYPE` reader - The value of bParityTpye set by software which is requested by GET_LINE_CODING command."]
pub type GET_BPARITY_TYPE_R = crate::FieldReader;
#[doc = "Field `GET_BPARITY_TYPE` writer - The value of bParityTpye set by software which is requested by GET_LINE_CODING command."]
pub type GET_BPARITY_TYPE_W<'a, REG> = crate::FieldWriter<'a, REG, 8>;
#[doc = "Field `GET_BCHAR_FORMAT` reader - The value of bDataBits set by software which is requested by GET_LINE_CODING command."]
pub type GET_BCHAR_FORMAT_R = crate::FieldReader;
#[doc = "Field `GET_BCHAR_FORMAT` writer - The value of bDataBits set by software which is requested by GET_LINE_CODING command."]
pub type GET_BCHAR_FORMAT_W<'a, REG> = crate::FieldWriter<'a, REG, 8>;
impl R {
    #[doc = "Bits 0:7 - The value of bCharFormat set by software which is requested by GET_LINE_CODING command."]
    #[inline(always)]
    pub fn get_bdata_bits(&self) -> GET_BDATA_BITS_R {
        GET_BDATA_BITS_R::new((self.bits & 0xff) as u8)
    }
    #[doc = "Bits 8:15 - The value of bParityTpye set by software which is requested by GET_LINE_CODING command."]
    #[inline(always)]
    pub fn get_bparity_type(&self) -> GET_BPARITY_TYPE_R {
        GET_BPARITY_TYPE_R::new(((self.bits >> 8) & 0xff) as u8)
    }
    #[doc = "Bits 16:23 - The value of bDataBits set by software which is requested by GET_LINE_CODING command."]
    #[inline(always)]
    pub fn get_bchar_format(&self) -> GET_BCHAR_FORMAT_R {
        GET_BCHAR_FORMAT_R::new(((self.bits >> 16) & 0xff) as u8)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("GET_LINE_CODE_W1")
            .field("get_bdata_bits", &self.get_bdata_bits())
            .field("get_bparity_type", &self.get_bparity_type())
            .field("get_bchar_format", &self.get_bchar_format())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:7 - The value of bCharFormat set by software which is requested by GET_LINE_CODING command."]
    #[inline(always)]
    pub fn get_bdata_bits(&mut self) -> GET_BDATA_BITS_W<'_, GET_LINE_CODE_W1_SPEC> {
        GET_BDATA_BITS_W::new(self, 0)
    }
    #[doc = "Bits 8:15 - The value of bParityTpye set by software which is requested by GET_LINE_CODING command."]
    #[inline(always)]
    pub fn get_bparity_type(&mut self) -> GET_BPARITY_TYPE_W<'_, GET_LINE_CODE_W1_SPEC> {
        GET_BPARITY_TYPE_W::new(self, 8)
    }
    #[doc = "Bits 16:23 - The value of bDataBits set by software which is requested by GET_LINE_CODING command."]
    #[inline(always)]
    pub fn get_bchar_format(&mut self) -> GET_BCHAR_FORMAT_W<'_, GET_LINE_CODE_W1_SPEC> {
        GET_BCHAR_FORMAT_W::new(self, 16)
    }
}
#[doc = "W1 of GET_LINE_CODING command.\n\nYou can [`read`](crate::Reg::read) this register and get [`get_line_code_w1::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`get_line_code_w1::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct GET_LINE_CODE_W1_SPEC;
impl crate::RegisterSpec for GET_LINE_CODE_W1_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`get_line_code_w1::R`](R) reader structure"]
impl crate::Readable for GET_LINE_CODE_W1_SPEC {}
#[doc = "`write(|w| ..)` method takes [`get_line_code_w1::W`](W) writer structure"]
impl crate::Writable for GET_LINE_CODE_W1_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets GET_LINE_CODE_W1 to value 0"]
impl crate::Resettable for GET_LINE_CODE_W1_SPEC {}
