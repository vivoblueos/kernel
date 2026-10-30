#[doc = "Register `GEN_CFG0` reader"]
pub type R = crate::R<GEN_CFG0_SPEC>;
#[doc = "Register `GEN_CFG0` writer"]
pub type W = crate::W<GEN_CFG0_SPEC>;
#[doc = "Field `CFG_UPMETHOD` reader - Update method for PWM generator 0's active register of configuration. When all bits are set to 0: immediately, when bit0 is set to 1: TEZ, when bit1 is set to 1:TEP,when bit2 is set to 1:sync,when bit3 is set to 1:disable the update"]
pub type CFG_UPMETHOD_R = crate::FieldReader;
#[doc = "Field `CFG_UPMETHOD` writer - Update method for PWM generator 0's active register of configuration. When all bits are set to 0: immediately, when bit0 is set to 1: TEZ, when bit1 is set to 1:TEP,when bit2 is set to 1:sync,when bit3 is set to 1:disable the update"]
pub type CFG_UPMETHOD_W<'a, REG> = crate::FieldWriter<'a, REG, 4>;
#[doc = "Field `T0_SEL` reader - Source selection for PWM generator 0 event_t0, take effect immediately, 0: fault_event0, 1: fault_event1, 2: fault_event2, 3: sync_taken, 4: none"]
pub type T0_SEL_R = crate::FieldReader;
#[doc = "Field `T0_SEL` writer - Source selection for PWM generator 0 event_t0, take effect immediately, 0: fault_event0, 1: fault_event1, 2: fault_event2, 3: sync_taken, 4: none"]
pub type T0_SEL_W<'a, REG> = crate::FieldWriter<'a, REG, 3>;
#[doc = "Field `T1_SEL` reader - Source selection for PWM generator 0 event_t1, take effect immediately, 0: fault_event0, 1: fault_event1, 2: fault_event2, 3: sync_taken, 4: none"]
pub type T1_SEL_R = crate::FieldReader;
#[doc = "Field `T1_SEL` writer - Source selection for PWM generator 0 event_t1, take effect immediately, 0: fault_event0, 1: fault_event1, 2: fault_event2, 3: sync_taken, 4: none"]
pub type T1_SEL_W<'a, REG> = crate::FieldWriter<'a, REG, 3>;
impl R {
    #[doc = "Bits 0:3 - Update method for PWM generator 0's active register of configuration. When all bits are set to 0: immediately, when bit0 is set to 1: TEZ, when bit1 is set to 1:TEP,when bit2 is set to 1:sync,when bit3 is set to 1:disable the update"]
    #[inline(always)]
    pub fn cfg_upmethod(&self) -> CFG_UPMETHOD_R {
        CFG_UPMETHOD_R::new((self.bits & 0x0f) as u8)
    }
    #[doc = "Bits 4:6 - Source selection for PWM generator 0 event_t0, take effect immediately, 0: fault_event0, 1: fault_event1, 2: fault_event2, 3: sync_taken, 4: none"]
    #[inline(always)]
    pub fn t0_sel(&self) -> T0_SEL_R {
        T0_SEL_R::new(((self.bits >> 4) & 7) as u8)
    }
    #[doc = "Bits 7:9 - Source selection for PWM generator 0 event_t1, take effect immediately, 0: fault_event0, 1: fault_event1, 2: fault_event2, 3: sync_taken, 4: none"]
    #[inline(always)]
    pub fn t1_sel(&self) -> T1_SEL_R {
        T1_SEL_R::new(((self.bits >> 7) & 7) as u8)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("GEN_CFG0")
            .field("cfg_upmethod", &self.cfg_upmethod())
            .field("t0_sel", &self.t0_sel())
            .field("t1_sel", &self.t1_sel())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:3 - Update method for PWM generator 0's active register of configuration. When all bits are set to 0: immediately, when bit0 is set to 1: TEZ, when bit1 is set to 1:TEP,when bit2 is set to 1:sync,when bit3 is set to 1:disable the update"]
    #[inline(always)]
    pub fn cfg_upmethod(&mut self) -> CFG_UPMETHOD_W<'_, GEN_CFG0_SPEC> {
        CFG_UPMETHOD_W::new(self, 0)
    }
    #[doc = "Bits 4:6 - Source selection for PWM generator 0 event_t0, take effect immediately, 0: fault_event0, 1: fault_event1, 2: fault_event2, 3: sync_taken, 4: none"]
    #[inline(always)]
    pub fn t0_sel(&mut self) -> T0_SEL_W<'_, GEN_CFG0_SPEC> {
        T0_SEL_W::new(self, 4)
    }
    #[doc = "Bits 7:9 - Source selection for PWM generator 0 event_t1, take effect immediately, 0: fault_event0, 1: fault_event1, 2: fault_event2, 3: sync_taken, 4: none"]
    #[inline(always)]
    pub fn t1_sel(&mut self) -> T1_SEL_W<'_, GEN_CFG0_SPEC> {
        T1_SEL_W::new(self, 7)
    }
}
#[doc = "Fault event T0 and T1 handling\n\nYou can [`read`](crate::Reg::read) this register and get [`gen_cfg0::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`gen_cfg0::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct GEN_CFG0_SPEC;
impl crate::RegisterSpec for GEN_CFG0_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`gen_cfg0::R`](R) reader structure"]
impl crate::Readable for GEN_CFG0_SPEC {}
#[doc = "`write(|w| ..)` method takes [`gen_cfg0::W`](W) writer structure"]
impl crate::Writable for GEN_CFG0_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets GEN_CFG0 to value 0"]
impl crate::Resettable for GEN_CFG0_SPEC {}
