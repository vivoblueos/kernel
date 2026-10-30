#[doc = "Register `MAC_ADDR1L` reader"]
pub type R = crate::R<MacAddr1lSpec>;
#[doc = "Register `MAC_ADDR1L` writer"]
pub type W = crate::W<MacAddr1lSpec>;
#[doc = "Field `ADDR1L` reader - MAC address1 low"]
pub type Addr1lR = crate::FieldReader<u32>;
#[doc = "Field `ADDR1L` writer - MAC address1 low"]
pub type Addr1lW<'a, REG> = crate::FieldWriter<'a, REG, 32, u32>;
impl R {
    #[doc = "Bits 0:31 - MAC address1 low"]
    #[inline(always)]
    pub fn addr1l(&self) -> Addr1lR {
        Addr1lR::new(self.bits)
    }
}
impl W {
    #[doc = "Bits 0:31 - MAC address1 low"]
    #[inline(always)]
    #[must_use]
    pub fn addr1l(&mut self) -> Addr1lW<MacAddr1lSpec> {
        Addr1lW::new(self, 0)
    }
}
#[doc = "Ethernet MAC address1 low register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`mac_addr1l::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`mac_addr1l::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct MacAddr1lSpec;
impl crate::RegisterSpec for MacAddr1lSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`mac_addr1l::R`](R) reader structure"]
impl crate::Readable for MacAddr1lSpec {}
#[doc = "`write(|w| ..)` method takes [`mac_addr1l::W`](W) writer structure"]
impl crate::Writable for MacAddr1lSpec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets MAC_ADDR1L to value 0xffff_ffff"]
impl crate::Resettable for MacAddr1lSpec {
    const RESET_VALUE: u32 = 0xffff_ffff;
}
