#[doc = "Register `UTIMECTL` reader"]
pub type R = crate::R<UTIMECTL_SPEC>;
#[doc = "Register `UTIMECTL` writer"]
pub type W = crate::W<UTIMECTL_SPEC>;
#[doc = "Field `UTIE` reader - Write 1 to enable the user timer interrupt."]
pub type UTIE_R = crate::BitReader;
#[doc = "Field `UTIE` writer - Write 1 to enable the user timer interrupt."]
pub type UTIE_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `UTIP` reader - Represents the pending status of the user timer interrupt."]
pub type UTIP_R = crate::BitReader;
#[doc = "Field `UTOF` reader - Configures whether the user timer overflows."]
pub type UTOF_R = crate::BitReader;
#[doc = "Field `UTOF` writer - Configures whether the user timer overflows."]
pub type UTOF_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 1 - Write 1 to enable the user timer interrupt."]
    #[inline(always)]
    pub fn utie(&self) -> UTIE_R {
        UTIE_R::new(((self.bits >> 1) & 1) != 0)
    }
    #[doc = "Bit 2 - Represents the pending status of the user timer interrupt."]
    #[inline(always)]
    pub fn utip(&self) -> UTIP_R {
        UTIP_R::new(((self.bits >> 2) & 1) != 0)
    }
    #[doc = "Bit 3 - Configures whether the user timer overflows."]
    #[inline(always)]
    pub fn utof(&self) -> UTOF_R {
        UTOF_R::new(((self.bits >> 3) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("UTIMECTL")
            .field("utie", &self.utie())
            .field("utip", &self.utip())
            .field("utof", &self.utof())
            .finish()
    }
}
impl W {
    #[doc = "Bit 1 - Write 1 to enable the user timer interrupt."]
    #[inline(always)]
    pub fn utie(&mut self) -> UTIE_W<'_, UTIMECTL_SPEC> {
        UTIE_W::new(self, 1)
    }
    #[doc = "Bit 3 - Configures whether the user timer overflows."]
    #[inline(always)]
    pub fn utof(&mut self) -> UTOF_W<'_, UTIMECTL_SPEC> {
        UTOF_W::new(self, 3)
    }
}
#[doc = "\n\nYou can [`read`](crate::Reg::read) this register and get [`utimectl::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`utimectl::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct UTIMECTL_SPEC;
impl crate::RegisterSpec for UTIMECTL_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`utimectl::R`](R) reader structure"]
impl crate::Readable for UTIMECTL_SPEC {}
#[doc = "`write(|w| ..)` method takes [`utimectl::W`](W) writer structure"]
impl crate::Writable for UTIMECTL_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets UTIMECTL to value 0"]
impl crate::Resettable for UTIMECTL_SPEC {}
