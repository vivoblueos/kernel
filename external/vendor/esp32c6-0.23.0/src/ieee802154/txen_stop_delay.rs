#[doc = "Register `TXEN_STOP_DELAY` reader"]
pub type R = crate::R<TXEN_STOP_DELAY_SPEC>;
#[doc = "Register `TXEN_STOP_DELAY` writer"]
pub type W = crate::W<TXEN_STOP_DELAY_SPEC>;
#[doc = "Field `TXEN_STOP_DLY` reader - "]
pub type TXEN_STOP_DLY_R = crate::FieldReader;
#[doc = "Field `TXEN_STOP_DLY` writer - "]
pub type TXEN_STOP_DLY_W<'a, REG> = crate::FieldWriter<'a, REG, 6>;
impl R {
    #[doc = "Bits 0:5"]
    #[inline(always)]
    pub fn txen_stop_dly(&self) -> TXEN_STOP_DLY_R {
        TXEN_STOP_DLY_R::new((self.bits & 0x3f) as u8)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("TXEN_STOP_DELAY")
            .field("txen_stop_dly", &self.txen_stop_dly())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:5"]
    #[inline(always)]
    pub fn txen_stop_dly(&mut self) -> TXEN_STOP_DLY_W<'_, TXEN_STOP_DELAY_SPEC> {
        TXEN_STOP_DLY_W::new(self, 0)
    }
}
#[doc = "\n\nYou can [`read`](crate::Reg::read) this register and get [`txen_stop_delay::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`txen_stop_delay::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct TXEN_STOP_DELAY_SPEC;
impl crate::RegisterSpec for TXEN_STOP_DELAY_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`txen_stop_delay::R`](R) reader structure"]
impl crate::Readable for TXEN_STOP_DELAY_SPEC {}
#[doc = "`write(|w| ..)` method takes [`txen_stop_delay::W`](W) writer structure"]
impl crate::Writable for TXEN_STOP_DELAY_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets TXEN_STOP_DELAY to value 0"]
impl crate::Resettable for TXEN_STOP_DELAY_SPEC {}
