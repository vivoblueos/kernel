#[doc = "Register `MODEM_DIAG_EN` reader"]
pub type R = crate::R<MODEM_DIAG_EN_SPEC>;
#[doc = "Register `MODEM_DIAG_EN` writer"]
pub type W = crate::W<MODEM_DIAG_EN_SPEC>;
#[doc = "Field `MODEM_DIAG_EN` reader - bit i to enable modem_diag\\[i\\] into gpio matrix. 1:enable modem_diag\\[i\\] into gpio matrix. 0:enable other signals into gpio matrix"]
pub type MODEM_DIAG_EN_R = crate::FieldReader<u32>;
#[doc = "Field `MODEM_DIAG_EN` writer - bit i to enable modem_diag\\[i\\] into gpio matrix. 1:enable modem_diag\\[i\\] into gpio matrix. 0:enable other signals into gpio matrix"]
pub type MODEM_DIAG_EN_W<'a, REG> = crate::FieldWriter<'a, REG, 32, u32>;
impl R {
    #[doc = "Bits 0:31 - bit i to enable modem_diag\\[i\\] into gpio matrix. 1:enable modem_diag\\[i\\] into gpio matrix. 0:enable other signals into gpio matrix"]
    #[inline(always)]
    pub fn modem_diag_en(&self) -> MODEM_DIAG_EN_R {
        MODEM_DIAG_EN_R::new(self.bits)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("MODEM_DIAG_EN")
            .field("modem_diag_en", &self.modem_diag_en())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:31 - bit i to enable modem_diag\\[i\\] into gpio matrix. 1:enable modem_diag\\[i\\] into gpio matrix. 0:enable other signals into gpio matrix"]
    #[inline(always)]
    pub fn modem_diag_en(&mut self) -> MODEM_DIAG_EN_W<'_, MODEM_DIAG_EN_SPEC> {
        MODEM_DIAG_EN_W::new(self, 0)
    }
}
#[doc = "GPIO MATRIX Configure Register for modem diag\n\nYou can [`read`](crate::Reg::read) this register and get [`modem_diag_en::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`modem_diag_en::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct MODEM_DIAG_EN_SPEC;
impl crate::RegisterSpec for MODEM_DIAG_EN_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`modem_diag_en::R`](R) reader structure"]
impl crate::Readable for MODEM_DIAG_EN_SPEC {}
#[doc = "`write(|w| ..)` method takes [`modem_diag_en::W`](W) writer structure"]
impl crate::Writable for MODEM_DIAG_EN_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets MODEM_DIAG_EN to value 0"]
impl crate::Resettable for MODEM_DIAG_EN_SPEC {}
