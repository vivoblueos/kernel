#[doc = "Register `MAC_ADDR0H` reader"]
pub type R = crate::R<MacAddr0hSpec>;
#[doc = "Register `MAC_ADDR0H` writer"]
pub type W = crate::W<MacAddr0hSpec>;
#[doc = "Field `ADDR0H` reader - MAC address0 high"]
pub type Addr0hR = crate::FieldReader<u16>;
#[doc = "Field `ADDR0H` writer - MAC address0 high"]
pub type Addr0hW<'a, REG> = crate::FieldWriter<'a, REG, 16, u16>;
#[doc = "Field `MO` reader - Always 1"]
pub type MoR = crate::BitReader;
#[doc = "Field `MO` writer - Always 1"]
pub type MoW<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bits 0:15 - MAC address0 high"]
    #[inline(always)]
    pub fn addr0h(&self) -> Addr0hR {
        Addr0hR::new((self.bits & 0xffff) as u16)
    }
    #[doc = "Bit 31 - Always 1"]
    #[inline(always)]
    pub fn mo(&self) -> MoR {
        MoR::new(((self.bits >> 31) & 1) != 0)
    }
}
impl W {
    #[doc = "Bits 0:15 - MAC address0 high"]
    #[inline(always)]
    #[must_use]
    pub fn addr0h(&mut self) -> Addr0hW<MacAddr0hSpec> {
        Addr0hW::new(self, 0)
    }
    #[doc = "Bit 31 - Always 1"]
    #[inline(always)]
    #[must_use]
    pub fn mo(&mut self) -> MoW<MacAddr0hSpec> {
        MoW::new(self, 31)
    }
}
#[doc = "Ethernet MAC address 0 high register (MAC_ADDR0H)\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`mac_addr0h::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`mac_addr0h::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct MacAddr0hSpec;
impl crate::RegisterSpec for MacAddr0hSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`mac_addr0h::R`](R) reader structure"]
impl crate::Readable for MacAddr0hSpec {}
#[doc = "`write(|w| ..)` method takes [`mac_addr0h::W`](W) writer structure"]
impl crate::Writable for MacAddr0hSpec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets MAC_ADDR0H to value 0x8000_ffff"]
impl crate::Resettable for MacAddr0hSpec {
    const RESET_VALUE: u32 = 0x8000_ffff;
}
