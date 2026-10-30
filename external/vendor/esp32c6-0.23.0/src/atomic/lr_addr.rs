#[doc = "Register `LR_ADDR` reader"]
pub type R = crate::R<LR_ADDR_SPEC>;
#[doc = "Register `LR_ADDR` writer"]
pub type W = crate::W<LR_ADDR_SPEC>;
#[doc = "Field `GLOABLE_LR_ADDR` reader - backup gloable address"]
pub type GLOABLE_LR_ADDR_R = crate::FieldReader<u32>;
#[doc = "Field `GLOABLE_LR_ADDR` writer - backup gloable address"]
pub type GLOABLE_LR_ADDR_W<'a, REG> = crate::FieldWriter<'a, REG, 32, u32>;
impl R {
    #[doc = "Bits 0:31 - backup gloable address"]
    #[inline(always)]
    pub fn gloable_lr_addr(&self) -> GLOABLE_LR_ADDR_R {
        GLOABLE_LR_ADDR_R::new(self.bits)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("LR_ADDR")
            .field("gloable_lr_addr", &self.gloable_lr_addr())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:31 - backup gloable address"]
    #[inline(always)]
    pub fn gloable_lr_addr(&mut self) -> GLOABLE_LR_ADDR_W<'_, LR_ADDR_SPEC> {
        GLOABLE_LR_ADDR_W::new(self, 0)
    }
}
#[doc = "gloable lr address regsiter\n\nYou can [`read`](crate::Reg::read) this register and get [`lr_addr::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`lr_addr::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct LR_ADDR_SPEC;
impl crate::RegisterSpec for LR_ADDR_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`lr_addr::R`](R) reader structure"]
impl crate::Readable for LR_ADDR_SPEC {}
#[doc = "`write(|w| ..)` method takes [`lr_addr::W`](W) writer structure"]
impl crate::Writable for LR_ADDR_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets LR_ADDR to value 0"]
impl crate::Resettable for LR_ADDR_SPEC {}
