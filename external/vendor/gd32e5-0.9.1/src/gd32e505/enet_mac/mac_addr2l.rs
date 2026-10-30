#[doc = "Register `MAC_ADDR2L` reader"]
pub type R = crate::R<MacAddr2lSpec>;
#[doc = "Register `MAC_ADDR2L` writer"]
pub type W = crate::W<MacAddr2lSpec>;
#[doc = "Field `ADDR2L` reader - MAC address2 low"]
pub type Addr2lR = crate::FieldReader<u32>;
#[doc = "Field `ADDR2L` writer - MAC address2 low"]
pub type Addr2lW<'a, REG> = crate::FieldWriter<'a, REG, 32, u32>;
impl R {
    #[doc = "Bits 0:31 - MAC address2 low"]
    #[inline(always)]
    pub fn addr2l(&self) -> Addr2lR {
        Addr2lR::new(self.bits)
    }
}
impl W {
    #[doc = "Bits 0:31 - MAC address2 low"]
    #[inline(always)]
    #[must_use]
    pub fn addr2l(&mut self) -> Addr2lW<MacAddr2lSpec> {
        Addr2lW::new(self, 0)
    }
}
#[doc = "Ethernet MAC address 2 low register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`mac_addr2l::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`mac_addr2l::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct MacAddr2lSpec;
impl crate::RegisterSpec for MacAddr2lSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`mac_addr2l::R`](R) reader structure"]
impl crate::Readable for MacAddr2lSpec {}
#[doc = "`write(|w| ..)` method takes [`mac_addr2l::W`](W) writer structure"]
impl crate::Writable for MacAddr2lSpec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets MAC_ADDR2L to value 0xffff_ffff"]
impl crate::Resettable for MacAddr2lSpec {
    const RESET_VALUE: u32 = 0xffff_ffff;
}
