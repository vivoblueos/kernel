#[doc = "Register `MAC_PHY_DATA` reader"]
pub type R = crate::R<MacPhyDataSpec>;
#[doc = "Register `MAC_PHY_DATA` writer"]
pub type W = crate::W<MacPhyDataSpec>;
#[doc = "Field `PD` reader - PHY data"]
pub type PdR = crate::FieldReader<u16>;
#[doc = "Field `PD` writer - PHY data"]
pub type PdW<'a, REG> = crate::FieldWriter<'a, REG, 16, u16>;
impl R {
    #[doc = "Bits 0:15 - PHY data"]
    #[inline(always)]
    pub fn pd(&self) -> PdR {
        PdR::new((self.bits & 0xffff) as u16)
    }
}
impl W {
    #[doc = "Bits 0:15 - PHY data"]
    #[inline(always)]
    #[must_use]
    pub fn pd(&mut self) -> PdW<MacPhyDataSpec> {
        PdW::new(self, 0)
    }
}
#[doc = "Ethernet MAC MII data register (MAC_PHY_DATA)\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`mac_phy_data::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`mac_phy_data::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct MacPhyDataSpec;
impl crate::RegisterSpec for MacPhyDataSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`mac_phy_data::R`](R) reader structure"]
impl crate::Readable for MacPhyDataSpec {}
#[doc = "`write(|w| ..)` method takes [`mac_phy_data::W`](W) writer structure"]
impl crate::Writable for MacPhyDataSpec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets MAC_PHY_DATA to value 0"]
impl crate::Resettable for MacPhyDataSpec {
    const RESET_VALUE: u32 = 0;
}
