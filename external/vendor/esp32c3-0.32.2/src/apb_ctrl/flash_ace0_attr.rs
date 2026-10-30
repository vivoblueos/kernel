#[doc = "Register `FLASH_ACE0_ATTR` reader"]
pub type R = crate::R<FLASH_ACE0_ATTR_SPEC>;
#[doc = "Register `FLASH_ACE0_ATTR` writer"]
pub type W = crate::W<FLASH_ACE0_ATTR_SPEC>;
#[doc = "Field `FLASH_ACE0_ATTR` reader - reg_flash_ace0_attr"]
pub type FLASH_ACE0_ATTR_R = crate::FieldReader;
#[doc = "Field `FLASH_ACE0_ATTR` writer - reg_flash_ace0_attr"]
pub type FLASH_ACE0_ATTR_W<'a, REG> = crate::FieldWriter<'a, REG, 2>;
impl R {
    #[doc = "Bits 0:1 - reg_flash_ace0_attr"]
    #[inline(always)]
    pub fn flash_ace0_attr(&self) -> FLASH_ACE0_ATTR_R {
        FLASH_ACE0_ATTR_R::new((self.bits & 3) as u8)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("FLASH_ACE0_ATTR")
            .field("flash_ace0_attr", &self.flash_ace0_attr())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:1 - reg_flash_ace0_attr"]
    #[inline(always)]
    pub fn flash_ace0_attr(&mut self) -> FLASH_ACE0_ATTR_W<'_, FLASH_ACE0_ATTR_SPEC> {
        FLASH_ACE0_ATTR_W::new(self, 0)
    }
}
#[doc = "APB_CTRL_FLASH_ACE0_ATTR_REG\n\nYou can [`read`](crate::Reg::read) this register and get [`flash_ace0_attr::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`flash_ace0_attr::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct FLASH_ACE0_ATTR_SPEC;
impl crate::RegisterSpec for FLASH_ACE0_ATTR_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`flash_ace0_attr::R`](R) reader structure"]
impl crate::Readable for FLASH_ACE0_ATTR_SPEC {}
#[doc = "`write(|w| ..)` method takes [`flash_ace0_attr::W`](W) writer structure"]
impl crate::Writable for FLASH_ACE0_ATTR_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets FLASH_ACE0_ATTR to value 0x03"]
impl crate::Resettable for FLASH_ACE0_ATTR_SPEC {
    const RESET_VALUE: u32 = 0x03;
}
