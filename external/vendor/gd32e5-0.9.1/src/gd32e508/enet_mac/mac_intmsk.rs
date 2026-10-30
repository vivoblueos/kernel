#[doc = "Register `MAC_INTMSK` reader"]
pub type R = crate::R<MacIntmskSpec>;
#[doc = "Register `MAC_INTMSK` writer"]
pub type W = crate::W<MacIntmskSpec>;
#[doc = "Field `WUMIM` reader - WUM interrupt mask"]
pub type WumimR = crate::BitReader;
#[doc = "Field `WUMIM` writer - WUM interrupt mask"]
pub type WumimW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `TMSTIM` reader - Time stamp trigger interrupt mask"]
pub type TmstimR = crate::BitReader;
#[doc = "Field `TMSTIM` writer - Time stamp trigger interrupt mask"]
pub type TmstimW<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 3 - WUM interrupt mask"]
    #[inline(always)]
    pub fn wumim(&self) -> WumimR {
        WumimR::new(((self.bits >> 3) & 1) != 0)
    }
    #[doc = "Bit 9 - Time stamp trigger interrupt mask"]
    #[inline(always)]
    pub fn tmstim(&self) -> TmstimR {
        TmstimR::new(((self.bits >> 9) & 1) != 0)
    }
}
impl W {
    #[doc = "Bit 3 - WUM interrupt mask"]
    #[inline(always)]
    #[must_use]
    pub fn wumim(&mut self) -> WumimW<MacIntmskSpec> {
        WumimW::new(self, 3)
    }
    #[doc = "Bit 9 - Time stamp trigger interrupt mask"]
    #[inline(always)]
    #[must_use]
    pub fn tmstim(&mut self) -> TmstimW<MacIntmskSpec> {
        TmstimW::new(self, 9)
    }
}
#[doc = "Ethernet MAC interrupt mask register (MAC_INTMSK)\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`mac_intmsk::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`mac_intmsk::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct MacIntmskSpec;
impl crate::RegisterSpec for MacIntmskSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`mac_intmsk::R`](R) reader structure"]
impl crate::Readable for MacIntmskSpec {}
#[doc = "`write(|w| ..)` method takes [`mac_intmsk::W`](W) writer structure"]
impl crate::Writable for MacIntmskSpec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets MAC_INTMSK to value 0"]
impl crate::Resettable for MacIntmskSpec {
    const RESET_VALUE: u32 = 0;
}
