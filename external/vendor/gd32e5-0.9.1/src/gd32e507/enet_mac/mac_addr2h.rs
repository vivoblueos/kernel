#[doc = "Register `MAC_ADDR2H` reader"]
pub type R = crate::R<MacAddr2hSpec>;
#[doc = "Register `MAC_ADDR2H` writer"]
pub type W = crate::W<MacAddr2hSpec>;
#[doc = "Field `ADDR2H` reader - Ethernet MAC address 2 high register"]
pub type Addr2hR = crate::FieldReader<u16>;
#[doc = "Field `ADDR2H` writer - Ethernet MAC address 2 high register"]
pub type Addr2hW<'a, REG> = crate::FieldWriter<'a, REG, 16, u16>;
#[doc = "Field `MB` reader - Mask byte"]
pub type MbR = crate::FieldReader;
#[doc = "Field `MB` writer - Mask byte"]
pub type MbW<'a, REG> = crate::FieldWriter<'a, REG, 6>;
#[doc = "Field `SAF` reader - Source address filter"]
pub type SafR = crate::BitReader;
#[doc = "Field `SAF` writer - Source address filter"]
pub type SafW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `AFE` reader - Address filter enable"]
pub type AfeR = crate::BitReader;
#[doc = "Field `AFE` writer - Address filter enable"]
pub type AfeW<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bits 0:15 - Ethernet MAC address 2 high register"]
    #[inline(always)]
    pub fn addr2h(&self) -> Addr2hR {
        Addr2hR::new((self.bits & 0xffff) as u16)
    }
    #[doc = "Bits 24:29 - Mask byte"]
    #[inline(always)]
    pub fn mb(&self) -> MbR {
        MbR::new(((self.bits >> 24) & 0x3f) as u8)
    }
    #[doc = "Bit 30 - Source address filter"]
    #[inline(always)]
    pub fn saf(&self) -> SafR {
        SafR::new(((self.bits >> 30) & 1) != 0)
    }
    #[doc = "Bit 31 - Address filter enable"]
    #[inline(always)]
    pub fn afe(&self) -> AfeR {
        AfeR::new(((self.bits >> 31) & 1) != 0)
    }
}
impl W {
    #[doc = "Bits 0:15 - Ethernet MAC address 2 high register"]
    #[inline(always)]
    #[must_use]
    pub fn addr2h(&mut self) -> Addr2hW<MacAddr2hSpec> {
        Addr2hW::new(self, 0)
    }
    #[doc = "Bits 24:29 - Mask byte"]
    #[inline(always)]
    #[must_use]
    pub fn mb(&mut self) -> MbW<MacAddr2hSpec> {
        MbW::new(self, 24)
    }
    #[doc = "Bit 30 - Source address filter"]
    #[inline(always)]
    #[must_use]
    pub fn saf(&mut self) -> SafW<MacAddr2hSpec> {
        SafW::new(self, 30)
    }
    #[doc = "Bit 31 - Address filter enable"]
    #[inline(always)]
    #[must_use]
    pub fn afe(&mut self) -> AfeW<MacAddr2hSpec> {
        AfeW::new(self, 31)
    }
}
#[doc = "Ethernet MAC address 2 high register (MAC_ADDR2H)\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`mac_addr2h::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`mac_addr2h::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct MacAddr2hSpec;
impl crate::RegisterSpec for MacAddr2hSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`mac_addr2h::R`](R) reader structure"]
impl crate::Readable for MacAddr2hSpec {}
#[doc = "`write(|w| ..)` method takes [`mac_addr2h::W`](W) writer structure"]
impl crate::Writable for MacAddr2hSpec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets MAC_ADDR2H to value 0xffff"]
impl crate::Resettable for MacAddr2hSpec {
    const RESET_VALUE: u32 = 0xffff;
}
