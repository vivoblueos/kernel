#[doc = "Register `REDUNDANT_ECO_CTRL` reader"]
pub type R = crate::R<REDUNDANT_ECO_CTRL_SPEC>;
#[doc = "Register `REDUNDANT_ECO_CTRL` writer"]
pub type W = crate::W<REDUNDANT_ECO_CTRL_SPEC>;
#[doc = "Field `REDUNDANT_ECO_DRIVE` reader - reg_redundant_eco_drive"]
pub type REDUNDANT_ECO_DRIVE_R = crate::BitReader;
#[doc = "Field `REDUNDANT_ECO_DRIVE` writer - reg_redundant_eco_drive"]
pub type REDUNDANT_ECO_DRIVE_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `REDUNDANT_ECO_RESULT` reader - reg_redundant_eco_result"]
pub type REDUNDANT_ECO_RESULT_R = crate::BitReader;
impl R {
    #[doc = "Bit 0 - reg_redundant_eco_drive"]
    #[inline(always)]
    pub fn redundant_eco_drive(&self) -> REDUNDANT_ECO_DRIVE_R {
        REDUNDANT_ECO_DRIVE_R::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - reg_redundant_eco_result"]
    #[inline(always)]
    pub fn redundant_eco_result(&self) -> REDUNDANT_ECO_RESULT_R {
        REDUNDANT_ECO_RESULT_R::new(((self.bits >> 1) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("REDUNDANT_ECO_CTRL")
            .field("redundant_eco_drive", &self.redundant_eco_drive())
            .field("redundant_eco_result", &self.redundant_eco_result())
            .finish()
    }
}
impl W {
    #[doc = "Bit 0 - reg_redundant_eco_drive"]
    #[inline(always)]
    pub fn redundant_eco_drive(&mut self) -> REDUNDANT_ECO_DRIVE_W<'_, REDUNDANT_ECO_CTRL_SPEC> {
        REDUNDANT_ECO_DRIVE_W::new(self, 0)
    }
}
#[doc = "eco register\n\nYou can [`read`](crate::Reg::read) this register and get [`redundant_eco_ctrl::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`redundant_eco_ctrl::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct REDUNDANT_ECO_CTRL_SPEC;
impl crate::RegisterSpec for REDUNDANT_ECO_CTRL_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`redundant_eco_ctrl::R`](R) reader structure"]
impl crate::Readable for REDUNDANT_ECO_CTRL_SPEC {}
#[doc = "`write(|w| ..)` method takes [`redundant_eco_ctrl::W`](W) writer structure"]
impl crate::Writable for REDUNDANT_ECO_CTRL_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets REDUNDANT_ECO_CTRL to value 0"]
impl crate::Resettable for REDUNDANT_ECO_CTRL_SPEC {}
