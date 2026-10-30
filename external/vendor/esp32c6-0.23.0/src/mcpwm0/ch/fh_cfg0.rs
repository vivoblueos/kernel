#[doc = "Register `FH_CFG0` reader"]
pub type R = crate::R<FH_CFG0_SPEC>;
#[doc = "Register `FH_CFG0` writer"]
pub type W = crate::W<FH_CFG0_SPEC>;
#[doc = "Field `SW_CBC` reader - Enable register for software force cycle-by-cycle mode action. 0: disable, 1: enable"]
pub type SW_CBC_R = crate::BitReader;
#[doc = "Field `SW_CBC` writer - Enable register for software force cycle-by-cycle mode action. 0: disable, 1: enable"]
pub type SW_CBC_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `F2_CBC` reader - event_f2 will trigger cycle-by-cycle mode action. 0: disable, 1: enable"]
pub type F2_CBC_R = crate::BitReader;
#[doc = "Field `F2_CBC` writer - event_f2 will trigger cycle-by-cycle mode action. 0: disable, 1: enable"]
pub type F2_CBC_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `F1_CBC` reader - event_f1 will trigger cycle-by-cycle mode action. 0: disable, 1: enable"]
pub type F1_CBC_R = crate::BitReader;
#[doc = "Field `F1_CBC` writer - event_f1 will trigger cycle-by-cycle mode action. 0: disable, 1: enable"]
pub type F1_CBC_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `F0_CBC` reader - event_f0 will trigger cycle-by-cycle mode action. 0: disable, 1: enable"]
pub type F0_CBC_R = crate::BitReader;
#[doc = "Field `F0_CBC` writer - event_f0 will trigger cycle-by-cycle mode action. 0: disable, 1: enable"]
pub type F0_CBC_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SW_OST` reader - Enable register for software force one-shot mode action. 0: disable, 1: enable"]
pub type SW_OST_R = crate::BitReader;
#[doc = "Field `SW_OST` writer - Enable register for software force one-shot mode action. 0: disable, 1: enable"]
pub type SW_OST_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `F2_OST` reader - event_f2 will trigger one-shot mode action. 0: disable, 1: enable"]
pub type F2_OST_R = crate::BitReader;
#[doc = "Field `F2_OST` writer - event_f2 will trigger one-shot mode action. 0: disable, 1: enable"]
pub type F2_OST_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `F1_OST` reader - event_f1 will trigger one-shot mode action. 0: disable, 1: enable"]
pub type F1_OST_R = crate::BitReader;
#[doc = "Field `F1_OST` writer - event_f1 will trigger one-shot mode action. 0: disable, 1: enable"]
pub type F1_OST_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `F0_OST` reader - event_f0 will trigger one-shot mode action. 0: disable, 1: enable"]
pub type F0_OST_R = crate::BitReader;
#[doc = "Field `F0_OST` writer - event_f0 will trigger one-shot mode action. 0: disable, 1: enable"]
pub type F0_OST_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `A_CBC_D` reader - Cycle-by-cycle mode action on PWM0A when fault event occurs and timer is decreasing. 0: do nothing, 1: force low, 2: force high, 3: toggle"]
pub type A_CBC_D_R = crate::FieldReader;
#[doc = "Field `A_CBC_D` writer - Cycle-by-cycle mode action on PWM0A when fault event occurs and timer is decreasing. 0: do nothing, 1: force low, 2: force high, 3: toggle"]
pub type A_CBC_D_W<'a, REG> = crate::FieldWriter<'a, REG, 2>;
#[doc = "Field `A_CBC_U` reader - Cycle-by-cycle mode action on PWM0A when fault event occurs and timer is increasing. 0: do nothing, 1: force low, 2: force high, 3: toggle"]
pub type A_CBC_U_R = crate::FieldReader;
#[doc = "Field `A_CBC_U` writer - Cycle-by-cycle mode action on PWM0A when fault event occurs and timer is increasing. 0: do nothing, 1: force low, 2: force high, 3: toggle"]
pub type A_CBC_U_W<'a, REG> = crate::FieldWriter<'a, REG, 2>;
#[doc = "Field `A_OST_D` reader - One-shot mode action on PWM0A when fault event occurs and timer is decreasing. 0: do nothing, 1: force low, 2: force high, 3: toggle"]
pub type A_OST_D_R = crate::FieldReader;
#[doc = "Field `A_OST_D` writer - One-shot mode action on PWM0A when fault event occurs and timer is decreasing. 0: do nothing, 1: force low, 2: force high, 3: toggle"]
pub type A_OST_D_W<'a, REG> = crate::FieldWriter<'a, REG, 2>;
#[doc = "Field `A_OST_U` reader - One-shot mode action on PWM0A when fault event occurs and timer is increasing. 0: do nothing, 1: force low, 2: force high, 3: toggle"]
pub type A_OST_U_R = crate::FieldReader;
#[doc = "Field `A_OST_U` writer - One-shot mode action on PWM0A when fault event occurs and timer is increasing. 0: do nothing, 1: force low, 2: force high, 3: toggle"]
pub type A_OST_U_W<'a, REG> = crate::FieldWriter<'a, REG, 2>;
#[doc = "Field `B_CBC_D` reader - Cycle-by-cycle mode action on PWM0B when fault event occurs and timer is decreasing. 0: do nothing, 1: force low, 2: force high, 3: toggle"]
pub type B_CBC_D_R = crate::FieldReader;
#[doc = "Field `B_CBC_D` writer - Cycle-by-cycle mode action on PWM0B when fault event occurs and timer is decreasing. 0: do nothing, 1: force low, 2: force high, 3: toggle"]
pub type B_CBC_D_W<'a, REG> = crate::FieldWriter<'a, REG, 2>;
#[doc = "Field `B_CBC_U` reader - Cycle-by-cycle mode action on PWM0B when fault event occurs and timer is increasing. 0: do nothing,1: force low, 2: force high, 3: toggle"]
pub type B_CBC_U_R = crate::FieldReader;
#[doc = "Field `B_CBC_U` writer - Cycle-by-cycle mode action on PWM0B when fault event occurs and timer is increasing. 0: do nothing,1: force low, 2: force high, 3: toggle"]
pub type B_CBC_U_W<'a, REG> = crate::FieldWriter<'a, REG, 2>;
#[doc = "Field `B_OST_D` reader - One-shot mode action on PWM0B when fault event occurs and timer is decreasing. 0: do nothing, 1: force low, 2: force high, 3: toggle"]
pub type B_OST_D_R = crate::FieldReader;
#[doc = "Field `B_OST_D` writer - One-shot mode action on PWM0B when fault event occurs and timer is decreasing. 0: do nothing, 1: force low, 2: force high, 3: toggle"]
pub type B_OST_D_W<'a, REG> = crate::FieldWriter<'a, REG, 2>;
#[doc = "Field `B_OST_U` reader - One-shot mode action on PWM0B when fault event occurs and timer is increasing. 0: do nothing, 1: force low, 2: force high, 3: toggle"]
pub type B_OST_U_R = crate::FieldReader;
#[doc = "Field `B_OST_U` writer - One-shot mode action on PWM0B when fault event occurs and timer is increasing. 0: do nothing, 1: force low, 2: force high, 3: toggle"]
pub type B_OST_U_W<'a, REG> = crate::FieldWriter<'a, REG, 2>;
impl R {
    #[doc = "Bit 0 - Enable register for software force cycle-by-cycle mode action. 0: disable, 1: enable"]
    #[inline(always)]
    pub fn sw_cbc(&self) -> SW_CBC_R {
        SW_CBC_R::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - event_f2 will trigger cycle-by-cycle mode action. 0: disable, 1: enable"]
    #[inline(always)]
    pub fn f2_cbc(&self) -> F2_CBC_R {
        F2_CBC_R::new(((self.bits >> 1) & 1) != 0)
    }
    #[doc = "Bit 2 - event_f1 will trigger cycle-by-cycle mode action. 0: disable, 1: enable"]
    #[inline(always)]
    pub fn f1_cbc(&self) -> F1_CBC_R {
        F1_CBC_R::new(((self.bits >> 2) & 1) != 0)
    }
    #[doc = "Bit 3 - event_f0 will trigger cycle-by-cycle mode action. 0: disable, 1: enable"]
    #[inline(always)]
    pub fn f0_cbc(&self) -> F0_CBC_R {
        F0_CBC_R::new(((self.bits >> 3) & 1) != 0)
    }
    #[doc = "Bit 4 - Enable register for software force one-shot mode action. 0: disable, 1: enable"]
    #[inline(always)]
    pub fn sw_ost(&self) -> SW_OST_R {
        SW_OST_R::new(((self.bits >> 4) & 1) != 0)
    }
    #[doc = "Bit 5 - event_f2 will trigger one-shot mode action. 0: disable, 1: enable"]
    #[inline(always)]
    pub fn f2_ost(&self) -> F2_OST_R {
        F2_OST_R::new(((self.bits >> 5) & 1) != 0)
    }
    #[doc = "Bit 6 - event_f1 will trigger one-shot mode action. 0: disable, 1: enable"]
    #[inline(always)]
    pub fn f1_ost(&self) -> F1_OST_R {
        F1_OST_R::new(((self.bits >> 6) & 1) != 0)
    }
    #[doc = "Bit 7 - event_f0 will trigger one-shot mode action. 0: disable, 1: enable"]
    #[inline(always)]
    pub fn f0_ost(&self) -> F0_OST_R {
        F0_OST_R::new(((self.bits >> 7) & 1) != 0)
    }
    #[doc = "Bits 8:9 - Cycle-by-cycle mode action on PWM0A when fault event occurs and timer is decreasing. 0: do nothing, 1: force low, 2: force high, 3: toggle"]
    #[inline(always)]
    pub fn a_cbc_d(&self) -> A_CBC_D_R {
        A_CBC_D_R::new(((self.bits >> 8) & 3) as u8)
    }
    #[doc = "Bits 10:11 - Cycle-by-cycle mode action on PWM0A when fault event occurs and timer is increasing. 0: do nothing, 1: force low, 2: force high, 3: toggle"]
    #[inline(always)]
    pub fn a_cbc_u(&self) -> A_CBC_U_R {
        A_CBC_U_R::new(((self.bits >> 10) & 3) as u8)
    }
    #[doc = "Bits 12:13 - One-shot mode action on PWM0A when fault event occurs and timer is decreasing. 0: do nothing, 1: force low, 2: force high, 3: toggle"]
    #[inline(always)]
    pub fn a_ost_d(&self) -> A_OST_D_R {
        A_OST_D_R::new(((self.bits >> 12) & 3) as u8)
    }
    #[doc = "Bits 14:15 - One-shot mode action on PWM0A when fault event occurs and timer is increasing. 0: do nothing, 1: force low, 2: force high, 3: toggle"]
    #[inline(always)]
    pub fn a_ost_u(&self) -> A_OST_U_R {
        A_OST_U_R::new(((self.bits >> 14) & 3) as u8)
    }
    #[doc = "Bits 16:17 - Cycle-by-cycle mode action on PWM0B when fault event occurs and timer is decreasing. 0: do nothing, 1: force low, 2: force high, 3: toggle"]
    #[inline(always)]
    pub fn b_cbc_d(&self) -> B_CBC_D_R {
        B_CBC_D_R::new(((self.bits >> 16) & 3) as u8)
    }
    #[doc = "Bits 18:19 - Cycle-by-cycle mode action on PWM0B when fault event occurs and timer is increasing. 0: do nothing,1: force low, 2: force high, 3: toggle"]
    #[inline(always)]
    pub fn b_cbc_u(&self) -> B_CBC_U_R {
        B_CBC_U_R::new(((self.bits >> 18) & 3) as u8)
    }
    #[doc = "Bits 20:21 - One-shot mode action on PWM0B when fault event occurs and timer is decreasing. 0: do nothing, 1: force low, 2: force high, 3: toggle"]
    #[inline(always)]
    pub fn b_ost_d(&self) -> B_OST_D_R {
        B_OST_D_R::new(((self.bits >> 20) & 3) as u8)
    }
    #[doc = "Bits 22:23 - One-shot mode action on PWM0B when fault event occurs and timer is increasing. 0: do nothing, 1: force low, 2: force high, 3: toggle"]
    #[inline(always)]
    pub fn b_ost_u(&self) -> B_OST_U_R {
        B_OST_U_R::new(((self.bits >> 22) & 3) as u8)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("FH_CFG0")
            .field("sw_cbc", &self.sw_cbc())
            .field("f2_cbc", &self.f2_cbc())
            .field("f1_cbc", &self.f1_cbc())
            .field("f0_cbc", &self.f0_cbc())
            .field("sw_ost", &self.sw_ost())
            .field("f2_ost", &self.f2_ost())
            .field("f1_ost", &self.f1_ost())
            .field("f0_ost", &self.f0_ost())
            .field("a_cbc_d", &self.a_cbc_d())
            .field("a_cbc_u", &self.a_cbc_u())
            .field("a_ost_d", &self.a_ost_d())
            .field("a_ost_u", &self.a_ost_u())
            .field("b_cbc_d", &self.b_cbc_d())
            .field("b_cbc_u", &self.b_cbc_u())
            .field("b_ost_d", &self.b_ost_d())
            .field("b_ost_u", &self.b_ost_u())
            .finish()
    }
}
impl W {
    #[doc = "Bit 0 - Enable register for software force cycle-by-cycle mode action. 0: disable, 1: enable"]
    #[inline(always)]
    pub fn sw_cbc(&mut self) -> SW_CBC_W<'_, FH_CFG0_SPEC> {
        SW_CBC_W::new(self, 0)
    }
    #[doc = "Bit 1 - event_f2 will trigger cycle-by-cycle mode action. 0: disable, 1: enable"]
    #[inline(always)]
    pub fn f2_cbc(&mut self) -> F2_CBC_W<'_, FH_CFG0_SPEC> {
        F2_CBC_W::new(self, 1)
    }
    #[doc = "Bit 2 - event_f1 will trigger cycle-by-cycle mode action. 0: disable, 1: enable"]
    #[inline(always)]
    pub fn f1_cbc(&mut self) -> F1_CBC_W<'_, FH_CFG0_SPEC> {
        F1_CBC_W::new(self, 2)
    }
    #[doc = "Bit 3 - event_f0 will trigger cycle-by-cycle mode action. 0: disable, 1: enable"]
    #[inline(always)]
    pub fn f0_cbc(&mut self) -> F0_CBC_W<'_, FH_CFG0_SPEC> {
        F0_CBC_W::new(self, 3)
    }
    #[doc = "Bit 4 - Enable register for software force one-shot mode action. 0: disable, 1: enable"]
    #[inline(always)]
    pub fn sw_ost(&mut self) -> SW_OST_W<'_, FH_CFG0_SPEC> {
        SW_OST_W::new(self, 4)
    }
    #[doc = "Bit 5 - event_f2 will trigger one-shot mode action. 0: disable, 1: enable"]
    #[inline(always)]
    pub fn f2_ost(&mut self) -> F2_OST_W<'_, FH_CFG0_SPEC> {
        F2_OST_W::new(self, 5)
    }
    #[doc = "Bit 6 - event_f1 will trigger one-shot mode action. 0: disable, 1: enable"]
    #[inline(always)]
    pub fn f1_ost(&mut self) -> F1_OST_W<'_, FH_CFG0_SPEC> {
        F1_OST_W::new(self, 6)
    }
    #[doc = "Bit 7 - event_f0 will trigger one-shot mode action. 0: disable, 1: enable"]
    #[inline(always)]
    pub fn f0_ost(&mut self) -> F0_OST_W<'_, FH_CFG0_SPEC> {
        F0_OST_W::new(self, 7)
    }
    #[doc = "Bits 8:9 - Cycle-by-cycle mode action on PWM0A when fault event occurs and timer is decreasing. 0: do nothing, 1: force low, 2: force high, 3: toggle"]
    #[inline(always)]
    pub fn a_cbc_d(&mut self) -> A_CBC_D_W<'_, FH_CFG0_SPEC> {
        A_CBC_D_W::new(self, 8)
    }
    #[doc = "Bits 10:11 - Cycle-by-cycle mode action on PWM0A when fault event occurs and timer is increasing. 0: do nothing, 1: force low, 2: force high, 3: toggle"]
    #[inline(always)]
    pub fn a_cbc_u(&mut self) -> A_CBC_U_W<'_, FH_CFG0_SPEC> {
        A_CBC_U_W::new(self, 10)
    }
    #[doc = "Bits 12:13 - One-shot mode action on PWM0A when fault event occurs and timer is decreasing. 0: do nothing, 1: force low, 2: force high, 3: toggle"]
    #[inline(always)]
    pub fn a_ost_d(&mut self) -> A_OST_D_W<'_, FH_CFG0_SPEC> {
        A_OST_D_W::new(self, 12)
    }
    #[doc = "Bits 14:15 - One-shot mode action on PWM0A when fault event occurs and timer is increasing. 0: do nothing, 1: force low, 2: force high, 3: toggle"]
    #[inline(always)]
    pub fn a_ost_u(&mut self) -> A_OST_U_W<'_, FH_CFG0_SPEC> {
        A_OST_U_W::new(self, 14)
    }
    #[doc = "Bits 16:17 - Cycle-by-cycle mode action on PWM0B when fault event occurs and timer is decreasing. 0: do nothing, 1: force low, 2: force high, 3: toggle"]
    #[inline(always)]
    pub fn b_cbc_d(&mut self) -> B_CBC_D_W<'_, FH_CFG0_SPEC> {
        B_CBC_D_W::new(self, 16)
    }
    #[doc = "Bits 18:19 - Cycle-by-cycle mode action on PWM0B when fault event occurs and timer is increasing. 0: do nothing,1: force low, 2: force high, 3: toggle"]
    #[inline(always)]
    pub fn b_cbc_u(&mut self) -> B_CBC_U_W<'_, FH_CFG0_SPEC> {
        B_CBC_U_W::new(self, 18)
    }
    #[doc = "Bits 20:21 - One-shot mode action on PWM0B when fault event occurs and timer is decreasing. 0: do nothing, 1: force low, 2: force high, 3: toggle"]
    #[inline(always)]
    pub fn b_ost_d(&mut self) -> B_OST_D_W<'_, FH_CFG0_SPEC> {
        B_OST_D_W::new(self, 20)
    }
    #[doc = "Bits 22:23 - One-shot mode action on PWM0B when fault event occurs and timer is increasing. 0: do nothing, 1: force low, 2: force high, 3: toggle"]
    #[inline(always)]
    pub fn b_ost_u(&mut self) -> B_OST_U_W<'_, FH_CFG0_SPEC> {
        B_OST_U_W::new(self, 22)
    }
}
#[doc = "Actions on PWM0A and PWM0B trip events\n\nYou can [`read`](crate::Reg::read) this register and get [`fh_cfg0::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`fh_cfg0::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct FH_CFG0_SPEC;
impl crate::RegisterSpec for FH_CFG0_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`fh_cfg0::R`](R) reader structure"]
impl crate::Readable for FH_CFG0_SPEC {}
#[doc = "`write(|w| ..)` method takes [`fh_cfg0::W`](W) writer structure"]
impl crate::Writable for FH_CFG0_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets FH_CFG0 to value 0"]
impl crate::Resettable for FH_CFG0_SPEC {}
