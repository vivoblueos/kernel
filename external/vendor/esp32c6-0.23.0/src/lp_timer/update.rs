#[doc = "Register `UPDATE` reader"]
pub type R = crate::R<UPDATE_SPEC>;
#[doc = "Register `UPDATE` writer"]
pub type W = crate::W<UPDATE_SPEC>;
#[doc = "Field `MAIN_TIMER_UPDATE` writer - need_des"]
pub type MAIN_TIMER_UPDATE_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `MAIN_TIMER_XTAL_OFF` reader - need_des"]
pub type MAIN_TIMER_XTAL_OFF_R = crate::BitReader;
#[doc = "Field `MAIN_TIMER_XTAL_OFF` writer - need_des"]
pub type MAIN_TIMER_XTAL_OFF_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `MAIN_TIMER_SYS_STALL` reader - need_des"]
pub type MAIN_TIMER_SYS_STALL_R = crate::BitReader;
#[doc = "Field `MAIN_TIMER_SYS_STALL` writer - need_des"]
pub type MAIN_TIMER_SYS_STALL_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `MAIN_TIMER_SYS_RST` reader - need_des"]
pub type MAIN_TIMER_SYS_RST_R = crate::BitReader;
#[doc = "Field `MAIN_TIMER_SYS_RST` writer - need_des"]
pub type MAIN_TIMER_SYS_RST_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 29 - need_des"]
    #[inline(always)]
    pub fn main_timer_xtal_off(&self) -> MAIN_TIMER_XTAL_OFF_R {
        MAIN_TIMER_XTAL_OFF_R::new(((self.bits >> 29) & 1) != 0)
    }
    #[doc = "Bit 30 - need_des"]
    #[inline(always)]
    pub fn main_timer_sys_stall(&self) -> MAIN_TIMER_SYS_STALL_R {
        MAIN_TIMER_SYS_STALL_R::new(((self.bits >> 30) & 1) != 0)
    }
    #[doc = "Bit 31 - need_des"]
    #[inline(always)]
    pub fn main_timer_sys_rst(&self) -> MAIN_TIMER_SYS_RST_R {
        MAIN_TIMER_SYS_RST_R::new(((self.bits >> 31) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("UPDATE")
            .field("main_timer_xtal_off", &self.main_timer_xtal_off())
            .field("main_timer_sys_stall", &self.main_timer_sys_stall())
            .field("main_timer_sys_rst", &self.main_timer_sys_rst())
            .finish()
    }
}
impl W {
    #[doc = "Bit 28 - need_des"]
    #[inline(always)]
    pub fn main_timer_update(&mut self) -> MAIN_TIMER_UPDATE_W<'_, UPDATE_SPEC> {
        MAIN_TIMER_UPDATE_W::new(self, 28)
    }
    #[doc = "Bit 29 - need_des"]
    #[inline(always)]
    pub fn main_timer_xtal_off(&mut self) -> MAIN_TIMER_XTAL_OFF_W<'_, UPDATE_SPEC> {
        MAIN_TIMER_XTAL_OFF_W::new(self, 29)
    }
    #[doc = "Bit 30 - need_des"]
    #[inline(always)]
    pub fn main_timer_sys_stall(&mut self) -> MAIN_TIMER_SYS_STALL_W<'_, UPDATE_SPEC> {
        MAIN_TIMER_SYS_STALL_W::new(self, 30)
    }
    #[doc = "Bit 31 - need_des"]
    #[inline(always)]
    pub fn main_timer_sys_rst(&mut self) -> MAIN_TIMER_SYS_RST_W<'_, UPDATE_SPEC> {
        MAIN_TIMER_SYS_RST_W::new(self, 31)
    }
}
#[doc = "need_des\n\nYou can [`read`](crate::Reg::read) this register and get [`update::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`update::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct UPDATE_SPEC;
impl crate::RegisterSpec for UPDATE_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`update::R`](R) reader structure"]
impl crate::Readable for UPDATE_SPEC {}
#[doc = "`write(|w| ..)` method takes [`update::W`](W) writer structure"]
impl crate::Writable for UPDATE_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets UPDATE to value 0"]
impl crate::Resettable for UPDATE_SPEC {}
