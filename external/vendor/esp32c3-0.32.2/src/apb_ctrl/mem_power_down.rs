#[doc = "Register `MEM_POWER_DOWN` reader"]
pub type R = crate::R<MEM_POWER_DOWN_SPEC>;
#[doc = "Register `MEM_POWER_DOWN` writer"]
pub type W = crate::W<MEM_POWER_DOWN_SPEC>;
#[doc = "Field `ROM_POWER_DOWN` reader - reg_rom_power_down"]
pub type ROM_POWER_DOWN_R = crate::FieldReader;
#[doc = "Field `ROM_POWER_DOWN` writer - reg_rom_power_down"]
pub type ROM_POWER_DOWN_W<'a, REG> = crate::FieldWriter<'a, REG, 2>;
#[doc = "Field `SRAM_POWER_DOWN` reader - reg_sram_power_down"]
pub type SRAM_POWER_DOWN_R = crate::FieldReader;
#[doc = "Field `SRAM_POWER_DOWN` writer - reg_sram_power_down"]
pub type SRAM_POWER_DOWN_W<'a, REG> = crate::FieldWriter<'a, REG, 4>;
impl R {
    #[doc = "Bits 0:1 - reg_rom_power_down"]
    #[inline(always)]
    pub fn rom_power_down(&self) -> ROM_POWER_DOWN_R {
        ROM_POWER_DOWN_R::new((self.bits & 3) as u8)
    }
    #[doc = "Bits 2:5 - reg_sram_power_down"]
    #[inline(always)]
    pub fn sram_power_down(&self) -> SRAM_POWER_DOWN_R {
        SRAM_POWER_DOWN_R::new(((self.bits >> 2) & 0x0f) as u8)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("MEM_POWER_DOWN")
            .field("rom_power_down", &self.rom_power_down())
            .field("sram_power_down", &self.sram_power_down())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:1 - reg_rom_power_down"]
    #[inline(always)]
    pub fn rom_power_down(&mut self) -> ROM_POWER_DOWN_W<'_, MEM_POWER_DOWN_SPEC> {
        ROM_POWER_DOWN_W::new(self, 0)
    }
    #[doc = "Bits 2:5 - reg_sram_power_down"]
    #[inline(always)]
    pub fn sram_power_down(&mut self) -> SRAM_POWER_DOWN_W<'_, MEM_POWER_DOWN_SPEC> {
        SRAM_POWER_DOWN_W::new(self, 2)
    }
}
#[doc = "APB_CTRL_MEM_POWER_DOWN_REG\n\nYou can [`read`](crate::Reg::read) this register and get [`mem_power_down::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`mem_power_down::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct MEM_POWER_DOWN_SPEC;
impl crate::RegisterSpec for MEM_POWER_DOWN_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`mem_power_down::R`](R) reader structure"]
impl crate::Readable for MEM_POWER_DOWN_SPEC {}
#[doc = "`write(|w| ..)` method takes [`mem_power_down::W`](W) writer structure"]
impl crate::Writable for MEM_POWER_DOWN_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets MEM_POWER_DOWN to value 0"]
impl crate::Resettable for MEM_POWER_DOWN_SPEC {}
