#[doc = "Register `BUS_TIMING_0` reader"]
pub type R = crate::R<BUS_TIMING_0_SPEC>;
#[doc = "Register `BUS_TIMING_0` writer"]
pub type W = crate::W<BUS_TIMING_0_SPEC>;
#[doc = "Field `BAUD_PRESC` reader - Baud Rate Prescaler, determines the frequency dividing ratio."]
pub type BAUD_PRESC_R = crate::FieldReader<u16>;
#[doc = "Field `BAUD_PRESC` writer - Baud Rate Prescaler, determines the frequency dividing ratio."]
pub type BAUD_PRESC_W<'a, REG> = crate::FieldWriter<'a, REG, 14, u16>;
#[doc = "Field `SYNC_JUMP_WIDTH` reader - Synchronization Jump Width (SJW), 1 \\verb+~+ 14 Tq wide."]
pub type SYNC_JUMP_WIDTH_R = crate::FieldReader;
#[doc = "Field `SYNC_JUMP_WIDTH` writer - Synchronization Jump Width (SJW), 1 \\verb+~+ 14 Tq wide."]
pub type SYNC_JUMP_WIDTH_W<'a, REG> = crate::FieldWriter<'a, REG, 2>;
impl R {
    #[doc = "Bits 0:13 - Baud Rate Prescaler, determines the frequency dividing ratio."]
    #[inline(always)]
    pub fn baud_presc(&self) -> BAUD_PRESC_R {
        BAUD_PRESC_R::new((self.bits & 0x3fff) as u16)
    }
    #[doc = "Bits 14:15 - Synchronization Jump Width (SJW), 1 \\verb+~+ 14 Tq wide."]
    #[inline(always)]
    pub fn sync_jump_width(&self) -> SYNC_JUMP_WIDTH_R {
        SYNC_JUMP_WIDTH_R::new(((self.bits >> 14) & 3) as u8)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("BUS_TIMING_0")
            .field("baud_presc", &self.baud_presc())
            .field("sync_jump_width", &self.sync_jump_width())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:13 - Baud Rate Prescaler, determines the frequency dividing ratio."]
    #[inline(always)]
    pub fn baud_presc(&mut self) -> BAUD_PRESC_W<'_, BUS_TIMING_0_SPEC> {
        BAUD_PRESC_W::new(self, 0)
    }
    #[doc = "Bits 14:15 - Synchronization Jump Width (SJW), 1 \\verb+~+ 14 Tq wide."]
    #[inline(always)]
    pub fn sync_jump_width(&mut self) -> SYNC_JUMP_WIDTH_W<'_, BUS_TIMING_0_SPEC> {
        SYNC_JUMP_WIDTH_W::new(self, 14)
    }
}
#[doc = "Bus Timing Register 0\n\nYou can [`read`](crate::Reg::read) this register and get [`bus_timing_0::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`bus_timing_0::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct BUS_TIMING_0_SPEC;
impl crate::RegisterSpec for BUS_TIMING_0_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`bus_timing_0::R`](R) reader structure"]
impl crate::Readable for BUS_TIMING_0_SPEC {}
#[doc = "`write(|w| ..)` method takes [`bus_timing_0::W`](W) writer structure"]
impl crate::Writable for BUS_TIMING_0_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets BUS_TIMING_0 to value 0"]
impl crate::Resettable for BUS_TIMING_0_SPEC {}
