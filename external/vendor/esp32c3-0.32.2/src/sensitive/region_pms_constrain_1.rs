#[doc = "Register `REGION_PMS_CONSTRAIN_1` reader"]
pub type R = crate::R<REGION_PMS_CONSTRAIN_1_SPEC>;
#[doc = "Register `REGION_PMS_CONSTRAIN_1` writer"]
pub type W = crate::W<REGION_PMS_CONSTRAIN_1_SPEC>;
#[doc = "Field `REGION_PMS_CONSTRAIN_WORLD_0_AREA_0` reader - region_pms_constrain_world_0_area_0"]
pub type REGION_PMS_CONSTRAIN_WORLD_0_AREA_0_R = crate::FieldReader;
#[doc = "Field `REGION_PMS_CONSTRAIN_WORLD_0_AREA_0` writer - region_pms_constrain_world_0_area_0"]
pub type REGION_PMS_CONSTRAIN_WORLD_0_AREA_0_W<'a, REG> = crate::FieldWriter<'a, REG, 2>;
#[doc = "Field `REGION_PMS_CONSTRAIN_WORLD_0_AREA_1` reader - region_pms_constrain_world_0_area_1"]
pub type REGION_PMS_CONSTRAIN_WORLD_0_AREA_1_R = crate::FieldReader;
#[doc = "Field `REGION_PMS_CONSTRAIN_WORLD_0_AREA_1` writer - region_pms_constrain_world_0_area_1"]
pub type REGION_PMS_CONSTRAIN_WORLD_0_AREA_1_W<'a, REG> = crate::FieldWriter<'a, REG, 2>;
#[doc = "Field `REGION_PMS_CONSTRAIN_WORLD_0_AREA_2` reader - region_pms_constrain_world_0_area_2"]
pub type REGION_PMS_CONSTRAIN_WORLD_0_AREA_2_R = crate::FieldReader;
#[doc = "Field `REGION_PMS_CONSTRAIN_WORLD_0_AREA_2` writer - region_pms_constrain_world_0_area_2"]
pub type REGION_PMS_CONSTRAIN_WORLD_0_AREA_2_W<'a, REG> = crate::FieldWriter<'a, REG, 2>;
#[doc = "Field `REGION_PMS_CONSTRAIN_WORLD_0_AREA_3` reader - region_pms_constrain_world_0_area_3"]
pub type REGION_PMS_CONSTRAIN_WORLD_0_AREA_3_R = crate::FieldReader;
#[doc = "Field `REGION_PMS_CONSTRAIN_WORLD_0_AREA_3` writer - region_pms_constrain_world_0_area_3"]
pub type REGION_PMS_CONSTRAIN_WORLD_0_AREA_3_W<'a, REG> = crate::FieldWriter<'a, REG, 2>;
#[doc = "Field `REGION_PMS_CONSTRAIN_WORLD_0_AREA_4` reader - region_pms_constrain_world_0_area_4"]
pub type REGION_PMS_CONSTRAIN_WORLD_0_AREA_4_R = crate::FieldReader;
#[doc = "Field `REGION_PMS_CONSTRAIN_WORLD_0_AREA_4` writer - region_pms_constrain_world_0_area_4"]
pub type REGION_PMS_CONSTRAIN_WORLD_0_AREA_4_W<'a, REG> = crate::FieldWriter<'a, REG, 2>;
#[doc = "Field `REGION_PMS_CONSTRAIN_WORLD_0_AREA_5` reader - region_pms_constrain_world_0_area_5"]
pub type REGION_PMS_CONSTRAIN_WORLD_0_AREA_5_R = crate::FieldReader;
#[doc = "Field `REGION_PMS_CONSTRAIN_WORLD_0_AREA_5` writer - region_pms_constrain_world_0_area_5"]
pub type REGION_PMS_CONSTRAIN_WORLD_0_AREA_5_W<'a, REG> = crate::FieldWriter<'a, REG, 2>;
#[doc = "Field `REGION_PMS_CONSTRAIN_WORLD_0_AREA_6` reader - region_pms_constrain_world_0_area_6"]
pub type REGION_PMS_CONSTRAIN_WORLD_0_AREA_6_R = crate::FieldReader;
#[doc = "Field `REGION_PMS_CONSTRAIN_WORLD_0_AREA_6` writer - region_pms_constrain_world_0_area_6"]
pub type REGION_PMS_CONSTRAIN_WORLD_0_AREA_6_W<'a, REG> = crate::FieldWriter<'a, REG, 2>;
impl R {
    #[doc = "Bits 0:1 - region_pms_constrain_world_0_area_0"]
    #[inline(always)]
    pub fn region_pms_constrain_world_0_area_0(&self) -> REGION_PMS_CONSTRAIN_WORLD_0_AREA_0_R {
        REGION_PMS_CONSTRAIN_WORLD_0_AREA_0_R::new((self.bits & 3) as u8)
    }
    #[doc = "Bits 2:3 - region_pms_constrain_world_0_area_1"]
    #[inline(always)]
    pub fn region_pms_constrain_world_0_area_1(&self) -> REGION_PMS_CONSTRAIN_WORLD_0_AREA_1_R {
        REGION_PMS_CONSTRAIN_WORLD_0_AREA_1_R::new(((self.bits >> 2) & 3) as u8)
    }
    #[doc = "Bits 4:5 - region_pms_constrain_world_0_area_2"]
    #[inline(always)]
    pub fn region_pms_constrain_world_0_area_2(&self) -> REGION_PMS_CONSTRAIN_WORLD_0_AREA_2_R {
        REGION_PMS_CONSTRAIN_WORLD_0_AREA_2_R::new(((self.bits >> 4) & 3) as u8)
    }
    #[doc = "Bits 6:7 - region_pms_constrain_world_0_area_3"]
    #[inline(always)]
    pub fn region_pms_constrain_world_0_area_3(&self) -> REGION_PMS_CONSTRAIN_WORLD_0_AREA_3_R {
        REGION_PMS_CONSTRAIN_WORLD_0_AREA_3_R::new(((self.bits >> 6) & 3) as u8)
    }
    #[doc = "Bits 8:9 - region_pms_constrain_world_0_area_4"]
    #[inline(always)]
    pub fn region_pms_constrain_world_0_area_4(&self) -> REGION_PMS_CONSTRAIN_WORLD_0_AREA_4_R {
        REGION_PMS_CONSTRAIN_WORLD_0_AREA_4_R::new(((self.bits >> 8) & 3) as u8)
    }
    #[doc = "Bits 10:11 - region_pms_constrain_world_0_area_5"]
    #[inline(always)]
    pub fn region_pms_constrain_world_0_area_5(&self) -> REGION_PMS_CONSTRAIN_WORLD_0_AREA_5_R {
        REGION_PMS_CONSTRAIN_WORLD_0_AREA_5_R::new(((self.bits >> 10) & 3) as u8)
    }
    #[doc = "Bits 12:13 - region_pms_constrain_world_0_area_6"]
    #[inline(always)]
    pub fn region_pms_constrain_world_0_area_6(&self) -> REGION_PMS_CONSTRAIN_WORLD_0_AREA_6_R {
        REGION_PMS_CONSTRAIN_WORLD_0_AREA_6_R::new(((self.bits >> 12) & 3) as u8)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("REGION_PMS_CONSTRAIN_1")
            .field(
                "region_pms_constrain_world_0_area_0",
                &self.region_pms_constrain_world_0_area_0(),
            )
            .field(
                "region_pms_constrain_world_0_area_1",
                &self.region_pms_constrain_world_0_area_1(),
            )
            .field(
                "region_pms_constrain_world_0_area_2",
                &self.region_pms_constrain_world_0_area_2(),
            )
            .field(
                "region_pms_constrain_world_0_area_3",
                &self.region_pms_constrain_world_0_area_3(),
            )
            .field(
                "region_pms_constrain_world_0_area_4",
                &self.region_pms_constrain_world_0_area_4(),
            )
            .field(
                "region_pms_constrain_world_0_area_5",
                &self.region_pms_constrain_world_0_area_5(),
            )
            .field(
                "region_pms_constrain_world_0_area_6",
                &self.region_pms_constrain_world_0_area_6(),
            )
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:1 - region_pms_constrain_world_0_area_0"]
    #[inline(always)]
    pub fn region_pms_constrain_world_0_area_0(
        &mut self,
    ) -> REGION_PMS_CONSTRAIN_WORLD_0_AREA_0_W<'_, REGION_PMS_CONSTRAIN_1_SPEC> {
        REGION_PMS_CONSTRAIN_WORLD_0_AREA_0_W::new(self, 0)
    }
    #[doc = "Bits 2:3 - region_pms_constrain_world_0_area_1"]
    #[inline(always)]
    pub fn region_pms_constrain_world_0_area_1(
        &mut self,
    ) -> REGION_PMS_CONSTRAIN_WORLD_0_AREA_1_W<'_, REGION_PMS_CONSTRAIN_1_SPEC> {
        REGION_PMS_CONSTRAIN_WORLD_0_AREA_1_W::new(self, 2)
    }
    #[doc = "Bits 4:5 - region_pms_constrain_world_0_area_2"]
    #[inline(always)]
    pub fn region_pms_constrain_world_0_area_2(
        &mut self,
    ) -> REGION_PMS_CONSTRAIN_WORLD_0_AREA_2_W<'_, REGION_PMS_CONSTRAIN_1_SPEC> {
        REGION_PMS_CONSTRAIN_WORLD_0_AREA_2_W::new(self, 4)
    }
    #[doc = "Bits 6:7 - region_pms_constrain_world_0_area_3"]
    #[inline(always)]
    pub fn region_pms_constrain_world_0_area_3(
        &mut self,
    ) -> REGION_PMS_CONSTRAIN_WORLD_0_AREA_3_W<'_, REGION_PMS_CONSTRAIN_1_SPEC> {
        REGION_PMS_CONSTRAIN_WORLD_0_AREA_3_W::new(self, 6)
    }
    #[doc = "Bits 8:9 - region_pms_constrain_world_0_area_4"]
    #[inline(always)]
    pub fn region_pms_constrain_world_0_area_4(
        &mut self,
    ) -> REGION_PMS_CONSTRAIN_WORLD_0_AREA_4_W<'_, REGION_PMS_CONSTRAIN_1_SPEC> {
        REGION_PMS_CONSTRAIN_WORLD_0_AREA_4_W::new(self, 8)
    }
    #[doc = "Bits 10:11 - region_pms_constrain_world_0_area_5"]
    #[inline(always)]
    pub fn region_pms_constrain_world_0_area_5(
        &mut self,
    ) -> REGION_PMS_CONSTRAIN_WORLD_0_AREA_5_W<'_, REGION_PMS_CONSTRAIN_1_SPEC> {
        REGION_PMS_CONSTRAIN_WORLD_0_AREA_5_W::new(self, 10)
    }
    #[doc = "Bits 12:13 - region_pms_constrain_world_0_area_6"]
    #[inline(always)]
    pub fn region_pms_constrain_world_0_area_6(
        &mut self,
    ) -> REGION_PMS_CONSTRAIN_WORLD_0_AREA_6_W<'_, REGION_PMS_CONSTRAIN_1_SPEC> {
        REGION_PMS_CONSTRAIN_WORLD_0_AREA_6_W::new(self, 12)
    }
}
#[doc = "SENSITIVE_REGION_PMS_CONSTRAIN_1_REG\n\nYou can [`read`](crate::Reg::read) this register and get [`region_pms_constrain_1::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`region_pms_constrain_1::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct REGION_PMS_CONSTRAIN_1_SPEC;
impl crate::RegisterSpec for REGION_PMS_CONSTRAIN_1_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`region_pms_constrain_1::R`](R) reader structure"]
impl crate::Readable for REGION_PMS_CONSTRAIN_1_SPEC {}
#[doc = "`write(|w| ..)` method takes [`region_pms_constrain_1::W`](W) writer structure"]
impl crate::Writable for REGION_PMS_CONSTRAIN_1_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets REGION_PMS_CONSTRAIN_1 to value 0x3fff"]
impl crate::Resettable for REGION_PMS_CONSTRAIN_1_SPEC {
    const RESET_VALUE: u32 = 0x3fff;
}
