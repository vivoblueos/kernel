#[doc = "Register `INT_CLR` reader"]
pub type R = crate::R<INT_CLR_SPEC>;
#[doc = "Register `INT_CLR` writer"]
pub type W = crate::W<INT_CLR_SPEC>;
#[doc = "Field `INT_CLR` reader - set this bit to clear RSA interrupt."]
pub type INT_CLR_R = crate::BitReader;
#[doc = "Field `INT_CLR` writer - set this bit to clear RSA interrupt."]
pub type INT_CLR_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 0 - set this bit to clear RSA interrupt."]
    #[inline(always)]
    pub fn int_clr(&self) -> INT_CLR_R {
        INT_CLR_R::new((self.bits & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("INT_CLR")
            .field("int_clr", &self.int_clr())
            .finish()
    }
}
impl W {
    #[doc = "Bit 0 - set this bit to clear RSA interrupt."]
    #[inline(always)]
    pub fn int_clr(&mut self) -> INT_CLR_W<'_, INT_CLR_SPEC> {
        INT_CLR_W::new(self, 0)
    }
}
#[doc = "RSA interrupt clear register\n\nYou can [`read`](crate::Reg::read) this register and get [`int_clr::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`int_clr::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct INT_CLR_SPEC;
impl crate::RegisterSpec for INT_CLR_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`int_clr::R`](R) reader structure"]
impl crate::Readable for INT_CLR_SPEC {}
#[doc = "`write(|w| ..)` method takes [`int_clr::W`](W) writer structure"]
impl crate::Writable for INT_CLR_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets INT_CLR to value 0"]
impl crate::Resettable for INT_CLR_SPEC {}
