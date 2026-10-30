#[doc = "Register `ID` reader"]
pub type R = crate::R<ID_SPEC>;
#[doc = "Register `ID` writer"]
pub type W = crate::W<ID_SPEC>;
#[doc = "Field `ID` reader - This register is used to configure the uart_id."]
pub type ID_R = crate::FieldReader<u32>;
#[doc = "Field `ID` writer - This register is used to configure the uart_id."]
pub type ID_W<'a, REG> = crate::FieldWriter<'a, REG, 32, u32>;
impl R {
    #[doc = "Bits 0:31 - This register is used to configure the uart_id."]
    #[inline(always)]
    pub fn id(&self) -> ID_R {
        ID_R::new(self.bits)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("ID").field("id", &self.id()).finish()
    }
}
impl W {
    #[doc = "Bits 0:31 - This register is used to configure the uart_id."]
    #[inline(always)]
    pub fn id(&mut self) -> ID_W<'_, ID_SPEC> {
        ID_W::new(self, 0)
    }
}
#[doc = "UART ID register\n\nYou can [`read`](crate::Reg::read) this register and get [`id::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`id::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct ID_SPEC;
impl crate::RegisterSpec for ID_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`id::R`](R) reader structure"]
impl crate::Readable for ID_SPEC {}
#[doc = "`write(|w| ..)` method takes [`id::W`](W) writer structure"]
impl crate::Writable for ID_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets ID to value 0x0500"]
impl crate::Resettable for ID_SPEC {
    const RESET_VALUE: u32 = 0x0500;
}
