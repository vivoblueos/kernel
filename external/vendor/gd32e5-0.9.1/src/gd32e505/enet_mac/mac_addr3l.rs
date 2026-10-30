#[doc = "Register `MAC_ADDR3L` reader"]
pub type R = crate::R<MacAddr3lSpec>;
#[doc = "Register `MAC_ADDR3L` writer"]
pub type W = crate::W<MacAddr3lSpec>;
#[doc = "Field `ADDR3L` reader - MAC address3 low"]
pub type Addr3lR = crate::FieldReader<u32>;
#[doc = "Field `ADDR3L` writer - MAC address3 low"]
pub type Addr3lW<'a, REG> = crate::FieldWriter<'a, REG, 32, u32>;
impl R {
    #[doc = "Bits 0:31 - MAC address3 low"]
    #[inline(always)]
    pub fn addr3l(&self) -> Addr3lR {
        Addr3lR::new(self.bits)
    }
}
impl W {
    #[doc = "Bits 0:31 - MAC address3 low"]
    #[inline(always)]
    #[must_use]
    pub fn addr3l(&mut self) -> Addr3lW<MacAddr3lSpec> {
        Addr3lW::new(self, 0)
    }
}
#[doc = "Ethernet MAC address 3 low register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`mac_addr3l::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`mac_addr3l::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct MacAddr3lSpec;
impl crate::RegisterSpec for MacAddr3lSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`mac_addr3l::R`](R) reader structure"]
impl crate::Readable for MacAddr3lSpec {}
#[doc = "`write(|w| ..)` method takes [`mac_addr3l::W`](W) writer structure"]
impl crate::Writable for MacAddr3lSpec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets MAC_ADDR3L to value 0xffff_ffff"]
impl crate::Resettable for MacAddr3lSpec {
    const RESET_VALUE: u32 = 0xffff_ffff;
}
