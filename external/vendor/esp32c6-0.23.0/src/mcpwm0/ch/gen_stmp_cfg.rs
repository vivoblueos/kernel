#[doc = "Register `GEN_STMP_CFG` reader"]
pub type R = crate::R<GEN_STMP_CFG_SPEC>;
#[doc = "Register `GEN_STMP_CFG` writer"]
pub type W = crate::W<GEN_STMP_CFG_SPEC>;
#[doc = "Field `A_UPMETHOD` reader - Update method for PWM generator 0 time stamp A's active register. When all bits are set to 0: immediately, when bit0 is set to 1: TEZ, when bit1 is set to 1: TEP,when bit2 is set to 1: sync, when bit3 is set to 1: disable the update."]
pub type A_UPMETHOD_R = crate::FieldReader;
#[doc = "Field `A_UPMETHOD` writer - Update method for PWM generator 0 time stamp A's active register. When all bits are set to 0: immediately, when bit0 is set to 1: TEZ, when bit1 is set to 1: TEP,when bit2 is set to 1: sync, when bit3 is set to 1: disable the update."]
pub type A_UPMETHOD_W<'a, REG> = crate::FieldWriter<'a, REG, 4>;
#[doc = "Field `B_UPMETHOD` reader - Update method for PWM generator 0 time stamp B's active register. When all bits are set to 0: immediately, when bit0 is set to 1: TEZ, when bit1 is set to 1: TEP,when bit2 is set to 1: sync, when bit3 is set to 1: disable the update."]
pub type B_UPMETHOD_R = crate::FieldReader;
#[doc = "Field `B_UPMETHOD` writer - Update method for PWM generator 0 time stamp B's active register. When all bits are set to 0: immediately, when bit0 is set to 1: TEZ, when bit1 is set to 1: TEP,when bit2 is set to 1: sync, when bit3 is set to 1: disable the update."]
pub type B_UPMETHOD_W<'a, REG> = crate::FieldWriter<'a, REG, 4>;
#[doc = "Field `A_SHDW_FULL` reader - Set and reset by hardware. If set, PWM generator 0 time stamp A's shadow reg is filled and waiting to be transferred to A's active reg. If cleared, A's active reg has been updated with shadow register latest value"]
pub type A_SHDW_FULL_R = crate::BitReader;
#[doc = "Field `A_SHDW_FULL` writer - Set and reset by hardware. If set, PWM generator 0 time stamp A's shadow reg is filled and waiting to be transferred to A's active reg. If cleared, A's active reg has been updated with shadow register latest value"]
pub type A_SHDW_FULL_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `B_SHDW_FULL` reader - Set and reset by hardware. If set, PWM generator 0 time stamp B's shadow reg is filled and waiting to be transferred to B's active reg. If cleared, B's active reg has been updated with shadow register latest value"]
pub type B_SHDW_FULL_R = crate::BitReader;
#[doc = "Field `B_SHDW_FULL` writer - Set and reset by hardware. If set, PWM generator 0 time stamp B's shadow reg is filled and waiting to be transferred to B's active reg. If cleared, B's active reg has been updated with shadow register latest value"]
pub type B_SHDW_FULL_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bits 0:3 - Update method for PWM generator 0 time stamp A's active register. When all bits are set to 0: immediately, when bit0 is set to 1: TEZ, when bit1 is set to 1: TEP,when bit2 is set to 1: sync, when bit3 is set to 1: disable the update."]
    #[inline(always)]
    pub fn a_upmethod(&self) -> A_UPMETHOD_R {
        A_UPMETHOD_R::new((self.bits & 0x0f) as u8)
    }
    #[doc = "Bits 4:7 - Update method for PWM generator 0 time stamp B's active register. When all bits are set to 0: immediately, when bit0 is set to 1: TEZ, when bit1 is set to 1: TEP,when bit2 is set to 1: sync, when bit3 is set to 1: disable the update."]
    #[inline(always)]
    pub fn b_upmethod(&self) -> B_UPMETHOD_R {
        B_UPMETHOD_R::new(((self.bits >> 4) & 0x0f) as u8)
    }
    #[doc = "Bit 8 - Set and reset by hardware. If set, PWM generator 0 time stamp A's shadow reg is filled and waiting to be transferred to A's active reg. If cleared, A's active reg has been updated with shadow register latest value"]
    #[inline(always)]
    pub fn a_shdw_full(&self) -> A_SHDW_FULL_R {
        A_SHDW_FULL_R::new(((self.bits >> 8) & 1) != 0)
    }
    #[doc = "Bit 9 - Set and reset by hardware. If set, PWM generator 0 time stamp B's shadow reg is filled and waiting to be transferred to B's active reg. If cleared, B's active reg has been updated with shadow register latest value"]
    #[inline(always)]
    pub fn b_shdw_full(&self) -> B_SHDW_FULL_R {
        B_SHDW_FULL_R::new(((self.bits >> 9) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("GEN_STMP_CFG")
            .field("a_upmethod", &self.a_upmethod())
            .field("b_upmethod", &self.b_upmethod())
            .field("a_shdw_full", &self.a_shdw_full())
            .field("b_shdw_full", &self.b_shdw_full())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:3 - Update method for PWM generator 0 time stamp A's active register. When all bits are set to 0: immediately, when bit0 is set to 1: TEZ, when bit1 is set to 1: TEP,when bit2 is set to 1: sync, when bit3 is set to 1: disable the update."]
    #[inline(always)]
    pub fn a_upmethod(&mut self) -> A_UPMETHOD_W<'_, GEN_STMP_CFG_SPEC> {
        A_UPMETHOD_W::new(self, 0)
    }
    #[doc = "Bits 4:7 - Update method for PWM generator 0 time stamp B's active register. When all bits are set to 0: immediately, when bit0 is set to 1: TEZ, when bit1 is set to 1: TEP,when bit2 is set to 1: sync, when bit3 is set to 1: disable the update."]
    #[inline(always)]
    pub fn b_upmethod(&mut self) -> B_UPMETHOD_W<'_, GEN_STMP_CFG_SPEC> {
        B_UPMETHOD_W::new(self, 4)
    }
    #[doc = "Bit 8 - Set and reset by hardware. If set, PWM generator 0 time stamp A's shadow reg is filled and waiting to be transferred to A's active reg. If cleared, A's active reg has been updated with shadow register latest value"]
    #[inline(always)]
    pub fn a_shdw_full(&mut self) -> A_SHDW_FULL_W<'_, GEN_STMP_CFG_SPEC> {
        A_SHDW_FULL_W::new(self, 8)
    }
    #[doc = "Bit 9 - Set and reset by hardware. If set, PWM generator 0 time stamp B's shadow reg is filled and waiting to be transferred to B's active reg. If cleared, B's active reg has been updated with shadow register latest value"]
    #[inline(always)]
    pub fn b_shdw_full(&mut self) -> B_SHDW_FULL_W<'_, GEN_STMP_CFG_SPEC> {
        B_SHDW_FULL_W::new(self, 9)
    }
}
#[doc = "Transfer status and update method for time stamp registers A and B\n\nYou can [`read`](crate::Reg::read) this register and get [`gen_stmp_cfg::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`gen_stmp_cfg::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct GEN_STMP_CFG_SPEC;
impl crate::RegisterSpec for GEN_STMP_CFG_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`gen_stmp_cfg::R`](R) reader structure"]
impl crate::Readable for GEN_STMP_CFG_SPEC {}
#[doc = "`write(|w| ..)` method takes [`gen_stmp_cfg::W`](W) writer structure"]
impl crate::Writable for GEN_STMP_CFG_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets GEN_STMP_CFG to value 0"]
impl crate::Resettable for GEN_STMP_CFG_SPEC {}
