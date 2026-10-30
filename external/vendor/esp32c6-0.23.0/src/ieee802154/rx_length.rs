#[doc = "Register `RX_LENGTH` reader"]
pub type R = crate::R<RX_LENGTH_SPEC>;
#[doc = "Register `RX_LENGTH` writer"]
pub type W = crate::W<RX_LENGTH_SPEC>;
#[doc = "Field `RX_LENGTH` reader - "]
pub type RX_LENGTH_R = crate::FieldReader;
#[doc = "Field `RX_LENGTH` writer - "]
pub type RX_LENGTH_W<'a, REG> = crate::FieldWriter<'a, REG, 7>;
impl R {
    #[doc = "Bits 0:6"]
    #[inline(always)]
    pub fn rx_length(&self) -> RX_LENGTH_R {
        RX_LENGTH_R::new((self.bits & 0x7f) as u8)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("RX_LENGTH")
            .field("rx_length", &self.rx_length())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:6"]
    #[inline(always)]
    pub fn rx_length(&mut self) -> RX_LENGTH_W<'_, RX_LENGTH_SPEC> {
        RX_LENGTH_W::new(self, 0)
    }
}
#[doc = "\n\nYou can [`read`](crate::Reg::read) this register and get [`rx_length::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`rx_length::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct RX_LENGTH_SPEC;
impl crate::RegisterSpec for RX_LENGTH_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`rx_length::R`](R) reader structure"]
impl crate::Readable for RX_LENGTH_SPEC {}
#[doc = "`write(|w| ..)` method takes [`rx_length::W`](W) writer structure"]
impl crate::Writable for RX_LENGTH_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets RX_LENGTH to value 0"]
impl crate::Resettable for RX_LENGTH_SPEC {}
