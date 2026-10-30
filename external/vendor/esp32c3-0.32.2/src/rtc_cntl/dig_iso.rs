#[doc = "Register `DIG_ISO` reader"]
pub type R = crate::R<DIG_ISO_SPEC>;
#[doc = "Register `DIG_ISO` writer"]
pub type W = crate::W<DIG_ISO_SPEC>;
#[doc = "Field `FORCE_OFF` reader - DIG_ISO force off"]
pub type FORCE_OFF_R = crate::BitReader;
#[doc = "Field `FORCE_OFF` writer - DIG_ISO force off"]
pub type FORCE_OFF_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `FORCE_ON` reader - DIG_ISO force on"]
pub type FORCE_ON_R = crate::BitReader;
#[doc = "Field `FORCE_ON` writer - DIG_ISO force on"]
pub type FORCE_ON_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `DG_PAD_AUTOHOLD` reader - read only register to indicate digital pad auto-hold status"]
pub type DG_PAD_AUTOHOLD_R = crate::BitReader;
#[doc = "Field `CLR_DG_PAD_AUTOHOLD` writer - wtite only register to clear digital pad auto-hold"]
pub type CLR_DG_PAD_AUTOHOLD_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `DG_PAD_AUTOHOLD_EN` reader - digital pad enable auto-hold"]
pub type DG_PAD_AUTOHOLD_EN_R = crate::BitReader;
#[doc = "Field `DG_PAD_AUTOHOLD_EN` writer - digital pad enable auto-hold"]
pub type DG_PAD_AUTOHOLD_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `DG_PAD_FORCE_NOISO` reader - digital pad force no ISO"]
pub type DG_PAD_FORCE_NOISO_R = crate::BitReader;
#[doc = "Field `DG_PAD_FORCE_NOISO` writer - digital pad force no ISO"]
pub type DG_PAD_FORCE_NOISO_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `DG_PAD_FORCE_ISO` reader - digital pad force ISO"]
pub type DG_PAD_FORCE_ISO_R = crate::BitReader;
#[doc = "Field `DG_PAD_FORCE_ISO` writer - digital pad force ISO"]
pub type DG_PAD_FORCE_ISO_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `DG_PAD_FORCE_UNHOLD` reader - digital pad force un-hold"]
pub type DG_PAD_FORCE_UNHOLD_R = crate::BitReader;
#[doc = "Field `DG_PAD_FORCE_UNHOLD` writer - digital pad force un-hold"]
pub type DG_PAD_FORCE_UNHOLD_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `DG_PAD_FORCE_HOLD` reader - digital pad force hold"]
pub type DG_PAD_FORCE_HOLD_R = crate::BitReader;
#[doc = "Field `DG_PAD_FORCE_HOLD` writer - digital pad force hold"]
pub type DG_PAD_FORCE_HOLD_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `BT_FORCE_ISO` reader - bt force ISO"]
pub type BT_FORCE_ISO_R = crate::BitReader;
#[doc = "Field `BT_FORCE_ISO` writer - bt force ISO"]
pub type BT_FORCE_ISO_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `BT_FORCE_NOISO` reader - bt force no ISO"]
pub type BT_FORCE_NOISO_R = crate::BitReader;
#[doc = "Field `BT_FORCE_NOISO` writer - bt force no ISO"]
pub type BT_FORCE_NOISO_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `DG_PERI_FORCE_ISO` reader - Digital peri force ISO"]
pub type DG_PERI_FORCE_ISO_R = crate::BitReader;
#[doc = "Field `DG_PERI_FORCE_ISO` writer - Digital peri force ISO"]
pub type DG_PERI_FORCE_ISO_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `DG_PERI_FORCE_NOISO` reader - digital peri force no ISO"]
pub type DG_PERI_FORCE_NOISO_R = crate::BitReader;
#[doc = "Field `DG_PERI_FORCE_NOISO` writer - digital peri force no ISO"]
pub type DG_PERI_FORCE_NOISO_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `CPU_TOP_FORCE_ISO` reader - cpu force ISO"]
pub type CPU_TOP_FORCE_ISO_R = crate::BitReader;
#[doc = "Field `CPU_TOP_FORCE_ISO` writer - cpu force ISO"]
pub type CPU_TOP_FORCE_ISO_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `CPU_TOP_FORCE_NOISO` reader - cpu force no ISO"]
pub type CPU_TOP_FORCE_NOISO_R = crate::BitReader;
#[doc = "Field `CPU_TOP_FORCE_NOISO` writer - cpu force no ISO"]
pub type CPU_TOP_FORCE_NOISO_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `WIFI_FORCE_ISO` reader - wifi force ISO"]
pub type WIFI_FORCE_ISO_R = crate::BitReader;
#[doc = "Field `WIFI_FORCE_ISO` writer - wifi force ISO"]
pub type WIFI_FORCE_ISO_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `WIFI_FORCE_NOISO` reader - wifi force no ISO"]
pub type WIFI_FORCE_NOISO_R = crate::BitReader;
#[doc = "Field `WIFI_FORCE_NOISO` writer - wifi force no ISO"]
pub type WIFI_FORCE_NOISO_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `DG_WRAP_FORCE_ISO` reader - digital core force ISO"]
pub type DG_WRAP_FORCE_ISO_R = crate::BitReader;
#[doc = "Field `DG_WRAP_FORCE_ISO` writer - digital core force ISO"]
pub type DG_WRAP_FORCE_ISO_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `DG_WRAP_FORCE_NOISO` reader - digital core force no ISO"]
pub type DG_WRAP_FORCE_NOISO_R = crate::BitReader;
#[doc = "Field `DG_WRAP_FORCE_NOISO` writer - digital core force no ISO"]
pub type DG_WRAP_FORCE_NOISO_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 7 - DIG_ISO force off"]
    #[inline(always)]
    pub fn force_off(&self) -> FORCE_OFF_R {
        FORCE_OFF_R::new(((self.bits >> 7) & 1) != 0)
    }
    #[doc = "Bit 8 - DIG_ISO force on"]
    #[inline(always)]
    pub fn force_on(&self) -> FORCE_ON_R {
        FORCE_ON_R::new(((self.bits >> 8) & 1) != 0)
    }
    #[doc = "Bit 9 - read only register to indicate digital pad auto-hold status"]
    #[inline(always)]
    pub fn dg_pad_autohold(&self) -> DG_PAD_AUTOHOLD_R {
        DG_PAD_AUTOHOLD_R::new(((self.bits >> 9) & 1) != 0)
    }
    #[doc = "Bit 11 - digital pad enable auto-hold"]
    #[inline(always)]
    pub fn dg_pad_autohold_en(&self) -> DG_PAD_AUTOHOLD_EN_R {
        DG_PAD_AUTOHOLD_EN_R::new(((self.bits >> 11) & 1) != 0)
    }
    #[doc = "Bit 12 - digital pad force no ISO"]
    #[inline(always)]
    pub fn dg_pad_force_noiso(&self) -> DG_PAD_FORCE_NOISO_R {
        DG_PAD_FORCE_NOISO_R::new(((self.bits >> 12) & 1) != 0)
    }
    #[doc = "Bit 13 - digital pad force ISO"]
    #[inline(always)]
    pub fn dg_pad_force_iso(&self) -> DG_PAD_FORCE_ISO_R {
        DG_PAD_FORCE_ISO_R::new(((self.bits >> 13) & 1) != 0)
    }
    #[doc = "Bit 14 - digital pad force un-hold"]
    #[inline(always)]
    pub fn dg_pad_force_unhold(&self) -> DG_PAD_FORCE_UNHOLD_R {
        DG_PAD_FORCE_UNHOLD_R::new(((self.bits >> 14) & 1) != 0)
    }
    #[doc = "Bit 15 - digital pad force hold"]
    #[inline(always)]
    pub fn dg_pad_force_hold(&self) -> DG_PAD_FORCE_HOLD_R {
        DG_PAD_FORCE_HOLD_R::new(((self.bits >> 15) & 1) != 0)
    }
    #[doc = "Bit 22 - bt force ISO"]
    #[inline(always)]
    pub fn bt_force_iso(&self) -> BT_FORCE_ISO_R {
        BT_FORCE_ISO_R::new(((self.bits >> 22) & 1) != 0)
    }
    #[doc = "Bit 23 - bt force no ISO"]
    #[inline(always)]
    pub fn bt_force_noiso(&self) -> BT_FORCE_NOISO_R {
        BT_FORCE_NOISO_R::new(((self.bits >> 23) & 1) != 0)
    }
    #[doc = "Bit 24 - Digital peri force ISO"]
    #[inline(always)]
    pub fn dg_peri_force_iso(&self) -> DG_PERI_FORCE_ISO_R {
        DG_PERI_FORCE_ISO_R::new(((self.bits >> 24) & 1) != 0)
    }
    #[doc = "Bit 25 - digital peri force no ISO"]
    #[inline(always)]
    pub fn dg_peri_force_noiso(&self) -> DG_PERI_FORCE_NOISO_R {
        DG_PERI_FORCE_NOISO_R::new(((self.bits >> 25) & 1) != 0)
    }
    #[doc = "Bit 26 - cpu force ISO"]
    #[inline(always)]
    pub fn cpu_top_force_iso(&self) -> CPU_TOP_FORCE_ISO_R {
        CPU_TOP_FORCE_ISO_R::new(((self.bits >> 26) & 1) != 0)
    }
    #[doc = "Bit 27 - cpu force no ISO"]
    #[inline(always)]
    pub fn cpu_top_force_noiso(&self) -> CPU_TOP_FORCE_NOISO_R {
        CPU_TOP_FORCE_NOISO_R::new(((self.bits >> 27) & 1) != 0)
    }
    #[doc = "Bit 28 - wifi force ISO"]
    #[inline(always)]
    pub fn wifi_force_iso(&self) -> WIFI_FORCE_ISO_R {
        WIFI_FORCE_ISO_R::new(((self.bits >> 28) & 1) != 0)
    }
    #[doc = "Bit 29 - wifi force no ISO"]
    #[inline(always)]
    pub fn wifi_force_noiso(&self) -> WIFI_FORCE_NOISO_R {
        WIFI_FORCE_NOISO_R::new(((self.bits >> 29) & 1) != 0)
    }
    #[doc = "Bit 30 - digital core force ISO"]
    #[inline(always)]
    pub fn dg_wrap_force_iso(&self) -> DG_WRAP_FORCE_ISO_R {
        DG_WRAP_FORCE_ISO_R::new(((self.bits >> 30) & 1) != 0)
    }
    #[doc = "Bit 31 - digital core force no ISO"]
    #[inline(always)]
    pub fn dg_wrap_force_noiso(&self) -> DG_WRAP_FORCE_NOISO_R {
        DG_WRAP_FORCE_NOISO_R::new(((self.bits >> 31) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("DIG_ISO")
            .field("force_off", &self.force_off())
            .field("force_on", &self.force_on())
            .field("dg_pad_autohold", &self.dg_pad_autohold())
            .field("dg_pad_autohold_en", &self.dg_pad_autohold_en())
            .field("dg_pad_force_noiso", &self.dg_pad_force_noiso())
            .field("dg_pad_force_iso", &self.dg_pad_force_iso())
            .field("dg_pad_force_unhold", &self.dg_pad_force_unhold())
            .field("dg_pad_force_hold", &self.dg_pad_force_hold())
            .field("bt_force_iso", &self.bt_force_iso())
            .field("bt_force_noiso", &self.bt_force_noiso())
            .field("dg_peri_force_iso", &self.dg_peri_force_iso())
            .field("dg_peri_force_noiso", &self.dg_peri_force_noiso())
            .field("cpu_top_force_iso", &self.cpu_top_force_iso())
            .field("cpu_top_force_noiso", &self.cpu_top_force_noiso())
            .field("wifi_force_iso", &self.wifi_force_iso())
            .field("wifi_force_noiso", &self.wifi_force_noiso())
            .field("dg_wrap_force_iso", &self.dg_wrap_force_iso())
            .field("dg_wrap_force_noiso", &self.dg_wrap_force_noiso())
            .finish()
    }
}
impl W {
    #[doc = "Bit 7 - DIG_ISO force off"]
    #[inline(always)]
    pub fn force_off(&mut self) -> FORCE_OFF_W<'_, DIG_ISO_SPEC> {
        FORCE_OFF_W::new(self, 7)
    }
    #[doc = "Bit 8 - DIG_ISO force on"]
    #[inline(always)]
    pub fn force_on(&mut self) -> FORCE_ON_W<'_, DIG_ISO_SPEC> {
        FORCE_ON_W::new(self, 8)
    }
    #[doc = "Bit 10 - wtite only register to clear digital pad auto-hold"]
    #[inline(always)]
    pub fn clr_dg_pad_autohold(&mut self) -> CLR_DG_PAD_AUTOHOLD_W<'_, DIG_ISO_SPEC> {
        CLR_DG_PAD_AUTOHOLD_W::new(self, 10)
    }
    #[doc = "Bit 11 - digital pad enable auto-hold"]
    #[inline(always)]
    pub fn dg_pad_autohold_en(&mut self) -> DG_PAD_AUTOHOLD_EN_W<'_, DIG_ISO_SPEC> {
        DG_PAD_AUTOHOLD_EN_W::new(self, 11)
    }
    #[doc = "Bit 12 - digital pad force no ISO"]
    #[inline(always)]
    pub fn dg_pad_force_noiso(&mut self) -> DG_PAD_FORCE_NOISO_W<'_, DIG_ISO_SPEC> {
        DG_PAD_FORCE_NOISO_W::new(self, 12)
    }
    #[doc = "Bit 13 - digital pad force ISO"]
    #[inline(always)]
    pub fn dg_pad_force_iso(&mut self) -> DG_PAD_FORCE_ISO_W<'_, DIG_ISO_SPEC> {
        DG_PAD_FORCE_ISO_W::new(self, 13)
    }
    #[doc = "Bit 14 - digital pad force un-hold"]
    #[inline(always)]
    pub fn dg_pad_force_unhold(&mut self) -> DG_PAD_FORCE_UNHOLD_W<'_, DIG_ISO_SPEC> {
        DG_PAD_FORCE_UNHOLD_W::new(self, 14)
    }
    #[doc = "Bit 15 - digital pad force hold"]
    #[inline(always)]
    pub fn dg_pad_force_hold(&mut self) -> DG_PAD_FORCE_HOLD_W<'_, DIG_ISO_SPEC> {
        DG_PAD_FORCE_HOLD_W::new(self, 15)
    }
    #[doc = "Bit 22 - bt force ISO"]
    #[inline(always)]
    pub fn bt_force_iso(&mut self) -> BT_FORCE_ISO_W<'_, DIG_ISO_SPEC> {
        BT_FORCE_ISO_W::new(self, 22)
    }
    #[doc = "Bit 23 - bt force no ISO"]
    #[inline(always)]
    pub fn bt_force_noiso(&mut self) -> BT_FORCE_NOISO_W<'_, DIG_ISO_SPEC> {
        BT_FORCE_NOISO_W::new(self, 23)
    }
    #[doc = "Bit 24 - Digital peri force ISO"]
    #[inline(always)]
    pub fn dg_peri_force_iso(&mut self) -> DG_PERI_FORCE_ISO_W<'_, DIG_ISO_SPEC> {
        DG_PERI_FORCE_ISO_W::new(self, 24)
    }
    #[doc = "Bit 25 - digital peri force no ISO"]
    #[inline(always)]
    pub fn dg_peri_force_noiso(&mut self) -> DG_PERI_FORCE_NOISO_W<'_, DIG_ISO_SPEC> {
        DG_PERI_FORCE_NOISO_W::new(self, 25)
    }
    #[doc = "Bit 26 - cpu force ISO"]
    #[inline(always)]
    pub fn cpu_top_force_iso(&mut self) -> CPU_TOP_FORCE_ISO_W<'_, DIG_ISO_SPEC> {
        CPU_TOP_FORCE_ISO_W::new(self, 26)
    }
    #[doc = "Bit 27 - cpu force no ISO"]
    #[inline(always)]
    pub fn cpu_top_force_noiso(&mut self) -> CPU_TOP_FORCE_NOISO_W<'_, DIG_ISO_SPEC> {
        CPU_TOP_FORCE_NOISO_W::new(self, 27)
    }
    #[doc = "Bit 28 - wifi force ISO"]
    #[inline(always)]
    pub fn wifi_force_iso(&mut self) -> WIFI_FORCE_ISO_W<'_, DIG_ISO_SPEC> {
        WIFI_FORCE_ISO_W::new(self, 28)
    }
    #[doc = "Bit 29 - wifi force no ISO"]
    #[inline(always)]
    pub fn wifi_force_noiso(&mut self) -> WIFI_FORCE_NOISO_W<'_, DIG_ISO_SPEC> {
        WIFI_FORCE_NOISO_W::new(self, 29)
    }
    #[doc = "Bit 30 - digital core force ISO"]
    #[inline(always)]
    pub fn dg_wrap_force_iso(&mut self) -> DG_WRAP_FORCE_ISO_W<'_, DIG_ISO_SPEC> {
        DG_WRAP_FORCE_ISO_W::new(self, 30)
    }
    #[doc = "Bit 31 - digital core force no ISO"]
    #[inline(always)]
    pub fn dg_wrap_force_noiso(&mut self) -> DG_WRAP_FORCE_NOISO_W<'_, DIG_ISO_SPEC> {
        DG_WRAP_FORCE_NOISO_W::new(self, 31)
    }
}
#[doc = "rtc configure register\n\nYou can [`read`](crate::Reg::read) this register and get [`dig_iso::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`dig_iso::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct DIG_ISO_SPEC;
impl crate::RegisterSpec for DIG_ISO_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`dig_iso::R`](R) reader structure"]
impl crate::Readable for DIG_ISO_SPEC {}
#[doc = "`write(|w| ..)` method takes [`dig_iso::W`](W) writer structure"]
impl crate::Writable for DIG_ISO_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets DIG_ISO to value 0xaa80_5080"]
impl crate::Resettable for DIG_ISO_SPEC {
    const RESET_VALUE: u32 = 0xaa80_5080;
}
