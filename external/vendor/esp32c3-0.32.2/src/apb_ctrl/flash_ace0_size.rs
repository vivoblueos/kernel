#[doc = "Register `FLASH_ACE0_SIZE` reader"]
pub type R = crate::R<FLASH_ACE0_SIZE_SPEC>;
#[doc = "Register `FLASH_ACE0_SIZE` writer"]
pub type W = crate::W<FLASH_ACE0_SIZE_SPEC>;
#[doc = "Field `FLASH_ACE0_SIZE` reader - reg_flash_ace0_size"]
pub type FLASH_ACE0_SIZE_R = crate::FieldReader<u16>;
#[doc = "Field `FLASH_ACE0_SIZE` writer - reg_flash_ace0_size"]
pub type FLASH_ACE0_SIZE_W<'a, REG> = crate::FieldWriter<'a, REG, 13, u16>;
impl R {
    #[doc = "Bits 0:12 - reg_flash_ace0_size"]
    #[inline(always)]
    pub fn flash_ace0_size(&self) -> FLASH_ACE0_SIZE_R {
        FLASH_ACE0_SIZE_R::new((self.bits & 0x1fff) as u16)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("FLASH_ACE0_SIZE")
            .field("flash_ace0_size", &self.flash_ace0_size())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:12 - reg_flash_ace0_size"]
    #[inline(always)]
    pub fn flash_ace0_size(&mut self) -> FLASH_ACE0_SIZE_W<'_, FLASH_ACE0_SIZE_SPEC> {
        FLASH_ACE0_SIZE_W::new(self, 0)
    }
}
#[doc = "APB_CTRL_FLASH_ACE0_SIZE_REG\n\nYou can [`read`](crate::Reg::read) this register and get [`flash_ace0_size::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`flash_ace0_size::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct FLASH_ACE0_SIZE_SPEC;
impl crate::RegisterSpec for FLASH_ACE0_SIZE_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`flash_ace0_size::R`](R) reader structure"]
impl crate::Readable for FLASH_ACE0_SIZE_SPEC {}
#[doc = "`write(|w| ..)` method takes [`flash_ace0_size::W`](W) writer structure"]
impl crate::Writable for FLASH_ACE0_SIZE_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets FLASH_ACE0_SIZE to value 0x0400"]
impl crate::Resettable for FLASH_ACE0_SIZE_SPEC {
    const RESET_VALUE: u32 = 0x0400;
}
