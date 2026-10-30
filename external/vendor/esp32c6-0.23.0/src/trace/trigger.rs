#[doc = "Register `TRIGGER` reader"]
pub type R = crate::R<TRIGGER_SPEC>;
#[doc = "Register `TRIGGER` writer"]
pub type W = crate::W<TRIGGER_SPEC>;
#[doc = "Field `ON` writer - 0\\] set 1 start trace."]
pub type ON_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `OFF` writer - set 1 stop trace."]
pub type OFF_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `MEM_LOOP` reader - if this reg is 1, trace will loop wrtie trace_mem. If is 0, when mem_current_addr at mem_end_addr, it will stop at the mem_end_addr"]
pub type MEM_LOOP_R = crate::BitReader;
#[doc = "Field `MEM_LOOP` writer - if this reg is 1, trace will loop wrtie trace_mem. If is 0, when mem_current_addr at mem_end_addr, it will stop at the mem_end_addr"]
pub type MEM_LOOP_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `RESTART_ENA` reader - enable encoder auto-restart, when lost package, the encoder will end, if enable auto-restart, when fifo empty, encoder will restart and send a sync package."]
pub type RESTART_ENA_R = crate::BitReader;
#[doc = "Field `RESTART_ENA` writer - enable encoder auto-restart, when lost package, the encoder will end, if enable auto-restart, when fifo empty, encoder will restart and send a sync package."]
pub type RESTART_ENA_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 2 - if this reg is 1, trace will loop wrtie trace_mem. If is 0, when mem_current_addr at mem_end_addr, it will stop at the mem_end_addr"]
    #[inline(always)]
    pub fn mem_loop(&self) -> MEM_LOOP_R {
        MEM_LOOP_R::new(((self.bits >> 2) & 1) != 0)
    }
    #[doc = "Bit 3 - enable encoder auto-restart, when lost package, the encoder will end, if enable auto-restart, when fifo empty, encoder will restart and send a sync package."]
    #[inline(always)]
    pub fn restart_ena(&self) -> RESTART_ENA_R {
        RESTART_ENA_R::new(((self.bits >> 3) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("TRIGGER")
            .field("mem_loop", &self.mem_loop())
            .field("restart_ena", &self.restart_ena())
            .finish()
    }
}
impl W {
    #[doc = "Bit 0 - 0\\] set 1 start trace."]
    #[inline(always)]
    pub fn on(&mut self) -> ON_W<'_, TRIGGER_SPEC> {
        ON_W::new(self, 0)
    }
    #[doc = "Bit 1 - set 1 stop trace."]
    #[inline(always)]
    pub fn off(&mut self) -> OFF_W<'_, TRIGGER_SPEC> {
        OFF_W::new(self, 1)
    }
    #[doc = "Bit 2 - if this reg is 1, trace will loop wrtie trace_mem. If is 0, when mem_current_addr at mem_end_addr, it will stop at the mem_end_addr"]
    #[inline(always)]
    pub fn mem_loop(&mut self) -> MEM_LOOP_W<'_, TRIGGER_SPEC> {
        MEM_LOOP_W::new(self, 2)
    }
    #[doc = "Bit 3 - enable encoder auto-restart, when lost package, the encoder will end, if enable auto-restart, when fifo empty, encoder will restart and send a sync package."]
    #[inline(always)]
    pub fn restart_ena(&mut self) -> RESTART_ENA_W<'_, TRIGGER_SPEC> {
        RESTART_ENA_W::new(self, 3)
    }
}
#[doc = "trigger register\n\nYou can [`read`](crate::Reg::read) this register and get [`trigger::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`trigger::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct TRIGGER_SPEC;
impl crate::RegisterSpec for TRIGGER_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`trigger::R`](R) reader structure"]
impl crate::Readable for TRIGGER_SPEC {}
#[doc = "`write(|w| ..)` method takes [`trigger::W`](W) writer structure"]
impl crate::Writable for TRIGGER_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets TRIGGER to value 0x0c"]
impl crate::Resettable for TRIGGER_SPEC {
    const RESET_VALUE: u32 = 0x0c;
}
