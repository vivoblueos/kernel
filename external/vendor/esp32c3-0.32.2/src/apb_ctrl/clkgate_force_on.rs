#[doc = "Register `CLKGATE_FORCE_ON` reader"]
pub type R = crate::R<CLKGATE_FORCE_ON_SPEC>;
#[doc = "Register `CLKGATE_FORCE_ON` writer"]
pub type W = crate::W<CLKGATE_FORCE_ON_SPEC>;
#[doc = "Field `ROM_CLKGATE_FORCE_ON` reader - reg_rom_clkgate_force_on"]
pub type ROM_CLKGATE_FORCE_ON_R = crate::FieldReader;
#[doc = "Field `ROM_CLKGATE_FORCE_ON` writer - reg_rom_clkgate_force_on"]
pub type ROM_CLKGATE_FORCE_ON_W<'a, REG> = crate::FieldWriter<'a, REG, 2>;
#[doc = "Field `SRAM_CLKGATE_FORCE_ON` reader - reg_sram_clkgate_force_on"]
pub type SRAM_CLKGATE_FORCE_ON_R = crate::FieldReader;
#[doc = "Field `SRAM_CLKGATE_FORCE_ON` writer - reg_sram_clkgate_force_on"]
pub type SRAM_CLKGATE_FORCE_ON_W<'a, REG> = crate::FieldWriter<'a, REG, 4>;
impl R {
    #[doc = "Bits 0:1 - reg_rom_clkgate_force_on"]
    #[inline(always)]
    pub fn rom_clkgate_force_on(&self) -> ROM_CLKGATE_FORCE_ON_R {
        ROM_CLKGATE_FORCE_ON_R::new((self.bits & 3) as u8)
    }
    #[doc = "Bits 2:5 - reg_sram_clkgate_force_on"]
    #[inline(always)]
    pub fn sram_clkgate_force_on(&self) -> SRAM_CLKGATE_FORCE_ON_R {
        SRAM_CLKGATE_FORCE_ON_R::new(((self.bits >> 2) & 0x0f) as u8)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("CLKGATE_FORCE_ON")
            .field("rom_clkgate_force_on", &self.rom_clkgate_force_on())
            .field("sram_clkgate_force_on", &self.sram_clkgate_force_on())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:1 - reg_rom_clkgate_force_on"]
    #[inline(always)]
    pub fn rom_clkgate_force_on(&mut self) -> ROM_CLKGATE_FORCE_ON_W<'_, CLKGATE_FORCE_ON_SPEC> {
        ROM_CLKGATE_FORCE_ON_W::new(self, 0)
    }
    #[doc = "Bits 2:5 - reg_sram_clkgate_force_on"]
    #[inline(always)]
    pub fn sram_clkgate_force_on(&mut self) -> SRAM_CLKGATE_FORCE_ON_W<'_, CLKGATE_FORCE_ON_SPEC> {
        SRAM_CLKGATE_FORCE_ON_W::new(self, 2)
    }
}
#[doc = "APB_CTRL_CLKGATE_FORCE_ON_REG\n\nYou can [`read`](crate::Reg::read) this register and get [`clkgate_force_on::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`clkgate_force_on::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct CLKGATE_FORCE_ON_SPEC;
impl crate::RegisterSpec for CLKGATE_FORCE_ON_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`clkgate_force_on::R`](R) reader structure"]
impl crate::Readable for CLKGATE_FORCE_ON_SPEC {}
#[doc = "`write(|w| ..)` method takes [`clkgate_force_on::W`](W) writer structure"]
impl crate::Writable for CLKGATE_FORCE_ON_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets CLKGATE_FORCE_ON to value 0x3f"]
impl crate::Resettable for CLKGATE_FORCE_ON_SPEC {
    const RESET_VALUE: u32 = 0x3f;
}
