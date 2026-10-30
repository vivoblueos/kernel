#[doc = "Register `SHORT_ADDR` reader"]
pub type R = crate::R<SHORT_ADDR_SPEC>;
#[doc = "Register `SHORT_ADDR` writer"]
pub type W = crate::W<SHORT_ADDR_SPEC>;
#[doc = "Field `SHORT_ADDR` reader - "]
pub type SHORT_ADDR_R = crate::FieldReader<u16>;
#[doc = "Field `SHORT_ADDR` writer - "]
pub type SHORT_ADDR_W<'a, REG> = crate::FieldWriter<'a, REG, 16, u16>;
impl R {
    #[doc = "Bits 0:15"]
    #[inline(always)]
    pub fn short_addr(&self) -> SHORT_ADDR_R {
        SHORT_ADDR_R::new((self.bits & 0xffff) as u16)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("SHORT_ADDR")
            .field("short_addr", &self.short_addr())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:15"]
    #[inline(always)]
    pub fn short_addr(&mut self) -> SHORT_ADDR_W<'_, SHORT_ADDR_SPEC> {
        SHORT_ADDR_W::new(self, 0)
    }
}
#[doc = "\n\nYou can [`read`](crate::Reg::read) this register and get [`short_addr::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`short_addr::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct SHORT_ADDR_SPEC;
impl crate::RegisterSpec for SHORT_ADDR_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`short_addr::R`](R) reader structure"]
impl crate::Readable for SHORT_ADDR_SPEC {}
#[doc = "`write(|w| ..)` method takes [`short_addr::W`](W) writer structure"]
impl crate::Writable for SHORT_ADDR_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets SHORT_ADDR to value 0"]
impl crate::Resettable for SHORT_ADDR_SPEC {}
