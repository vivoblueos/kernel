#[doc = "Register `MAC_RWFF` reader"]
pub type R = crate::R<MacRwffSpec>;
#[doc = "Register `MAC_RWFF` writer"]
pub type W = crate::W<MacRwffSpec>;
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        write!(f, "{}", self.bits())
    }
}
impl core::fmt::Debug for crate::generic::Reg<MacRwffSpec> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        core::fmt::Debug::fmt(&self.read(), f)
    }
}
impl W {}
#[doc = "Ethernet MAC remote wakeup frame filter register (MAC_RWFF)\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`mac_rwff::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`mac_rwff::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct MacRwffSpec;
impl crate::RegisterSpec for MacRwffSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`mac_rwff::R`](R) reader structure"]
impl crate::Readable for MacRwffSpec {}
#[doc = "`write(|w| ..)` method takes [`mac_rwff::W`](W) writer structure"]
impl crate::Writable for MacRwffSpec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets MAC_RWFF to value 0"]
impl crate::Resettable for MacRwffSpec {
    const RESET_VALUE: u32 = 0;
}
