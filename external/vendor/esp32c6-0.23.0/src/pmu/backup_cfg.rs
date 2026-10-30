#[doc = "Register `BACKUP_CFG` reader"]
pub type R = crate::R<BACKUP_CFG_SPEC>;
#[doc = "Register `BACKUP_CFG` writer"]
pub type W = crate::W<BACKUP_CFG_SPEC>;
#[doc = "Field `BACKUP_SYS_CLK_NO_DIV` reader - need_des"]
pub type BACKUP_SYS_CLK_NO_DIV_R = crate::BitReader;
#[doc = "Field `BACKUP_SYS_CLK_NO_DIV` writer - need_des"]
pub type BACKUP_SYS_CLK_NO_DIV_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 31 - need_des"]
    #[inline(always)]
    pub fn backup_sys_clk_no_div(&self) -> BACKUP_SYS_CLK_NO_DIV_R {
        BACKUP_SYS_CLK_NO_DIV_R::new(((self.bits >> 31) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("BACKUP_CFG")
            .field("backup_sys_clk_no_div", &self.backup_sys_clk_no_div())
            .finish()
    }
}
impl W {
    #[doc = "Bit 31 - need_des"]
    #[inline(always)]
    pub fn backup_sys_clk_no_div(&mut self) -> BACKUP_SYS_CLK_NO_DIV_W<'_, BACKUP_CFG_SPEC> {
        BACKUP_SYS_CLK_NO_DIV_W::new(self, 31)
    }
}
#[doc = "need_des\n\nYou can [`read`](crate::Reg::read) this register and get [`backup_cfg::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`backup_cfg::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct BACKUP_CFG_SPEC;
impl crate::RegisterSpec for BACKUP_CFG_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`backup_cfg::R`](R) reader structure"]
impl crate::Readable for BACKUP_CFG_SPEC {}
#[doc = "`write(|w| ..)` method takes [`backup_cfg::W`](W) writer structure"]
impl crate::Writable for BACKUP_CFG_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets BACKUP_CFG to value 0x8000_0000"]
impl crate::Resettable for BACKUP_CFG_SPEC {
    const RESET_VALUE: u32 = 0x8000_0000;
}
