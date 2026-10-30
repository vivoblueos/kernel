#[doc = "Register `MTIMECTL` reader"]
pub type R = crate::R<MTIMECTL_SPEC>;
#[doc = "Register `MTIMECTL` writer"]
pub type W = crate::W<MTIMECTL_SPEC>;
#[doc = "Field `MTCE` reader - Configures whether to enable the CLINT timer counter."]
pub type MTCE_R = crate::BitReader;
#[doc = "Field `MTCE` writer - Configures whether to enable the CLINT timer counter."]
pub type MTCE_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `MTIE` reader - Write 1 to enable the machine timer interrupt."]
pub type MTIE_R = crate::BitReader;
#[doc = "Field `MTIE` writer - Write 1 to enable the machine timer interrupt."]
pub type MTIE_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `MTIP` reader - Represents the pending status of the machine timer interrupt."]
pub type MTIP_R = crate::BitReader;
#[doc = "Field `MTOF` reader - Configures whether the machine timer overflows."]
pub type MTOF_R = crate::BitReader;
#[doc = "Field `MTOF` writer - Configures whether the machine timer overflows."]
pub type MTOF_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 0 - Configures whether to enable the CLINT timer counter."]
    #[inline(always)]
    pub fn mtce(&self) -> MTCE_R {
        MTCE_R::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - Write 1 to enable the machine timer interrupt."]
    #[inline(always)]
    pub fn mtie(&self) -> MTIE_R {
        MTIE_R::new(((self.bits >> 1) & 1) != 0)
    }
    #[doc = "Bit 2 - Represents the pending status of the machine timer interrupt."]
    #[inline(always)]
    pub fn mtip(&self) -> MTIP_R {
        MTIP_R::new(((self.bits >> 2) & 1) != 0)
    }
    #[doc = "Bit 3 - Configures whether the machine timer overflows."]
    #[inline(always)]
    pub fn mtof(&self) -> MTOF_R {
        MTOF_R::new(((self.bits >> 3) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("MTIMECTL")
            .field("mtce", &self.mtce())
            .field("mtie", &self.mtie())
            .field("mtip", &self.mtip())
            .field("mtof", &self.mtof())
            .finish()
    }
}
impl W {
    #[doc = "Bit 0 - Configures whether to enable the CLINT timer counter."]
    #[inline(always)]
    pub fn mtce(&mut self) -> MTCE_W<'_, MTIMECTL_SPEC> {
        MTCE_W::new(self, 0)
    }
    #[doc = "Bit 1 - Write 1 to enable the machine timer interrupt."]
    #[inline(always)]
    pub fn mtie(&mut self) -> MTIE_W<'_, MTIMECTL_SPEC> {
        MTIE_W::new(self, 1)
    }
    #[doc = "Bit 3 - Configures whether the machine timer overflows."]
    #[inline(always)]
    pub fn mtof(&mut self) -> MTOF_W<'_, MTIMECTL_SPEC> {
        MTOF_W::new(self, 3)
    }
}
#[doc = "\n\nYou can [`read`](crate::Reg::read) this register and get [`mtimectl::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`mtimectl::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct MTIMECTL_SPEC;
impl crate::RegisterSpec for MTIMECTL_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`mtimectl::R`](R) reader structure"]
impl crate::Readable for MTIMECTL_SPEC {}
#[doc = "`write(|w| ..)` method takes [`mtimectl::W`](W) writer structure"]
impl crate::Writable for MTIMECTL_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets MTIMECTL to value 0"]
impl crate::Resettable for MTIMECTL_SPEC {}
