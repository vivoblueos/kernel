#[doc = "Register `MONTR_ENA` reader"]
pub type R = crate::R<MONTR_ENA_SPEC>;
#[doc = "Register `MONTR_ENA` writer"]
pub type W = crate::W<MONTR_ENA_SPEC>;
#[doc = "Field `AREA_DRAM0_0_RD_ENA` reader - Core0 dram0 area0 read monitor enable"]
pub type AREA_DRAM0_0_RD_ENA_R = crate::BitReader;
#[doc = "Field `AREA_DRAM0_0_RD_ENA` writer - Core0 dram0 area0 read monitor enable"]
pub type AREA_DRAM0_0_RD_ENA_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `AREA_DRAM0_0_WR_ENA` reader - Core0 dram0 area0 write monitor enable"]
pub type AREA_DRAM0_0_WR_ENA_R = crate::BitReader;
#[doc = "Field `AREA_DRAM0_0_WR_ENA` writer - Core0 dram0 area0 write monitor enable"]
pub type AREA_DRAM0_0_WR_ENA_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `AREA_DRAM0_1_RD_ENA` reader - Core0 dram0 area1 read monitor enable"]
pub type AREA_DRAM0_1_RD_ENA_R = crate::BitReader;
#[doc = "Field `AREA_DRAM0_1_RD_ENA` writer - Core0 dram0 area1 read monitor enable"]
pub type AREA_DRAM0_1_RD_ENA_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `AREA_DRAM0_1_WR_ENA` reader - Core0 dram0 area1 write monitor enable"]
pub type AREA_DRAM0_1_WR_ENA_R = crate::BitReader;
#[doc = "Field `AREA_DRAM0_1_WR_ENA` writer - Core0 dram0 area1 write monitor enable"]
pub type AREA_DRAM0_1_WR_ENA_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `AREA_PIF_0_RD_ENA` reader - Core0 PIF area0 read monitor enable"]
pub type AREA_PIF_0_RD_ENA_R = crate::BitReader;
#[doc = "Field `AREA_PIF_0_RD_ENA` writer - Core0 PIF area0 read monitor enable"]
pub type AREA_PIF_0_RD_ENA_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `AREA_PIF_0_WR_ENA` reader - Core0 PIF area0 write monitor enable"]
pub type AREA_PIF_0_WR_ENA_R = crate::BitReader;
#[doc = "Field `AREA_PIF_0_WR_ENA` writer - Core0 PIF area0 write monitor enable"]
pub type AREA_PIF_0_WR_ENA_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `AREA_PIF_1_RD_ENA` reader - Core0 PIF area1 read monitor enable"]
pub type AREA_PIF_1_RD_ENA_R = crate::BitReader;
#[doc = "Field `AREA_PIF_1_RD_ENA` writer - Core0 PIF area1 read monitor enable"]
pub type AREA_PIF_1_RD_ENA_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `AREA_PIF_1_WR_ENA` reader - Core0 PIF area1 write monitor enable"]
pub type AREA_PIF_1_WR_ENA_R = crate::BitReader;
#[doc = "Field `AREA_PIF_1_WR_ENA` writer - Core0 PIF area1 write monitor enable"]
pub type AREA_PIF_1_WR_ENA_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SP_SPILL_MIN_ENA` reader - Core0 stackpoint underflow monitor enable"]
pub type SP_SPILL_MIN_ENA_R = crate::BitReader;
#[doc = "Field `SP_SPILL_MIN_ENA` writer - Core0 stackpoint underflow monitor enable"]
pub type SP_SPILL_MIN_ENA_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SP_SPILL_MAX_ENA` reader - Core0 stackpoint overflow monitor enable"]
pub type SP_SPILL_MAX_ENA_R = crate::BitReader;
#[doc = "Field `SP_SPILL_MAX_ENA` writer - Core0 stackpoint overflow monitor enable"]
pub type SP_SPILL_MAX_ENA_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `IRAM0_EXCEPTION_MONITOR_ENA` reader - IBUS busy monitor enable"]
pub type IRAM0_EXCEPTION_MONITOR_ENA_R = crate::BitReader;
#[doc = "Field `IRAM0_EXCEPTION_MONITOR_ENA` writer - IBUS busy monitor enable"]
pub type IRAM0_EXCEPTION_MONITOR_ENA_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `DRAM0_EXCEPTION_MONITOR_ENA` reader - DBUS busy monitor enbale"]
pub type DRAM0_EXCEPTION_MONITOR_ENA_R = crate::BitReader;
#[doc = "Field `DRAM0_EXCEPTION_MONITOR_ENA` writer - DBUS busy monitor enbale"]
pub type DRAM0_EXCEPTION_MONITOR_ENA_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 0 - Core0 dram0 area0 read monitor enable"]
    #[inline(always)]
    pub fn area_dram0_0_rd_ena(&self) -> AREA_DRAM0_0_RD_ENA_R {
        AREA_DRAM0_0_RD_ENA_R::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - Core0 dram0 area0 write monitor enable"]
    #[inline(always)]
    pub fn area_dram0_0_wr_ena(&self) -> AREA_DRAM0_0_WR_ENA_R {
        AREA_DRAM0_0_WR_ENA_R::new(((self.bits >> 1) & 1) != 0)
    }
    #[doc = "Bit 2 - Core0 dram0 area1 read monitor enable"]
    #[inline(always)]
    pub fn area_dram0_1_rd_ena(&self) -> AREA_DRAM0_1_RD_ENA_R {
        AREA_DRAM0_1_RD_ENA_R::new(((self.bits >> 2) & 1) != 0)
    }
    #[doc = "Bit 3 - Core0 dram0 area1 write monitor enable"]
    #[inline(always)]
    pub fn area_dram0_1_wr_ena(&self) -> AREA_DRAM0_1_WR_ENA_R {
        AREA_DRAM0_1_WR_ENA_R::new(((self.bits >> 3) & 1) != 0)
    }
    #[doc = "Bit 4 - Core0 PIF area0 read monitor enable"]
    #[inline(always)]
    pub fn area_pif_0_rd_ena(&self) -> AREA_PIF_0_RD_ENA_R {
        AREA_PIF_0_RD_ENA_R::new(((self.bits >> 4) & 1) != 0)
    }
    #[doc = "Bit 5 - Core0 PIF area0 write monitor enable"]
    #[inline(always)]
    pub fn area_pif_0_wr_ena(&self) -> AREA_PIF_0_WR_ENA_R {
        AREA_PIF_0_WR_ENA_R::new(((self.bits >> 5) & 1) != 0)
    }
    #[doc = "Bit 6 - Core0 PIF area1 read monitor enable"]
    #[inline(always)]
    pub fn area_pif_1_rd_ena(&self) -> AREA_PIF_1_RD_ENA_R {
        AREA_PIF_1_RD_ENA_R::new(((self.bits >> 6) & 1) != 0)
    }
    #[doc = "Bit 7 - Core0 PIF area1 write monitor enable"]
    #[inline(always)]
    pub fn area_pif_1_wr_ena(&self) -> AREA_PIF_1_WR_ENA_R {
        AREA_PIF_1_WR_ENA_R::new(((self.bits >> 7) & 1) != 0)
    }
    #[doc = "Bit 8 - Core0 stackpoint underflow monitor enable"]
    #[inline(always)]
    pub fn sp_spill_min_ena(&self) -> SP_SPILL_MIN_ENA_R {
        SP_SPILL_MIN_ENA_R::new(((self.bits >> 8) & 1) != 0)
    }
    #[doc = "Bit 9 - Core0 stackpoint overflow monitor enable"]
    #[inline(always)]
    pub fn sp_spill_max_ena(&self) -> SP_SPILL_MAX_ENA_R {
        SP_SPILL_MAX_ENA_R::new(((self.bits >> 9) & 1) != 0)
    }
    #[doc = "Bit 10 - IBUS busy monitor enable"]
    #[inline(always)]
    pub fn iram0_exception_monitor_ena(&self) -> IRAM0_EXCEPTION_MONITOR_ENA_R {
        IRAM0_EXCEPTION_MONITOR_ENA_R::new(((self.bits >> 10) & 1) != 0)
    }
    #[doc = "Bit 11 - DBUS busy monitor enbale"]
    #[inline(always)]
    pub fn dram0_exception_monitor_ena(&self) -> DRAM0_EXCEPTION_MONITOR_ENA_R {
        DRAM0_EXCEPTION_MONITOR_ENA_R::new(((self.bits >> 11) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("MONTR_ENA")
            .field("area_dram0_0_rd_ena", &self.area_dram0_0_rd_ena())
            .field("area_dram0_0_wr_ena", &self.area_dram0_0_wr_ena())
            .field("area_dram0_1_rd_ena", &self.area_dram0_1_rd_ena())
            .field("area_dram0_1_wr_ena", &self.area_dram0_1_wr_ena())
            .field("area_pif_0_rd_ena", &self.area_pif_0_rd_ena())
            .field("area_pif_0_wr_ena", &self.area_pif_0_wr_ena())
            .field("area_pif_1_rd_ena", &self.area_pif_1_rd_ena())
            .field("area_pif_1_wr_ena", &self.area_pif_1_wr_ena())
            .field("sp_spill_min_ena", &self.sp_spill_min_ena())
            .field("sp_spill_max_ena", &self.sp_spill_max_ena())
            .field(
                "iram0_exception_monitor_ena",
                &self.iram0_exception_monitor_ena(),
            )
            .field(
                "dram0_exception_monitor_ena",
                &self.dram0_exception_monitor_ena(),
            )
            .finish()
    }
}
impl W {
    #[doc = "Bit 0 - Core0 dram0 area0 read monitor enable"]
    #[inline(always)]
    pub fn area_dram0_0_rd_ena(&mut self) -> AREA_DRAM0_0_RD_ENA_W<'_, MONTR_ENA_SPEC> {
        AREA_DRAM0_0_RD_ENA_W::new(self, 0)
    }
    #[doc = "Bit 1 - Core0 dram0 area0 write monitor enable"]
    #[inline(always)]
    pub fn area_dram0_0_wr_ena(&mut self) -> AREA_DRAM0_0_WR_ENA_W<'_, MONTR_ENA_SPEC> {
        AREA_DRAM0_0_WR_ENA_W::new(self, 1)
    }
    #[doc = "Bit 2 - Core0 dram0 area1 read monitor enable"]
    #[inline(always)]
    pub fn area_dram0_1_rd_ena(&mut self) -> AREA_DRAM0_1_RD_ENA_W<'_, MONTR_ENA_SPEC> {
        AREA_DRAM0_1_RD_ENA_W::new(self, 2)
    }
    #[doc = "Bit 3 - Core0 dram0 area1 write monitor enable"]
    #[inline(always)]
    pub fn area_dram0_1_wr_ena(&mut self) -> AREA_DRAM0_1_WR_ENA_W<'_, MONTR_ENA_SPEC> {
        AREA_DRAM0_1_WR_ENA_W::new(self, 3)
    }
    #[doc = "Bit 4 - Core0 PIF area0 read monitor enable"]
    #[inline(always)]
    pub fn area_pif_0_rd_ena(&mut self) -> AREA_PIF_0_RD_ENA_W<'_, MONTR_ENA_SPEC> {
        AREA_PIF_0_RD_ENA_W::new(self, 4)
    }
    #[doc = "Bit 5 - Core0 PIF area0 write monitor enable"]
    #[inline(always)]
    pub fn area_pif_0_wr_ena(&mut self) -> AREA_PIF_0_WR_ENA_W<'_, MONTR_ENA_SPEC> {
        AREA_PIF_0_WR_ENA_W::new(self, 5)
    }
    #[doc = "Bit 6 - Core0 PIF area1 read monitor enable"]
    #[inline(always)]
    pub fn area_pif_1_rd_ena(&mut self) -> AREA_PIF_1_RD_ENA_W<'_, MONTR_ENA_SPEC> {
        AREA_PIF_1_RD_ENA_W::new(self, 6)
    }
    #[doc = "Bit 7 - Core0 PIF area1 write monitor enable"]
    #[inline(always)]
    pub fn area_pif_1_wr_ena(&mut self) -> AREA_PIF_1_WR_ENA_W<'_, MONTR_ENA_SPEC> {
        AREA_PIF_1_WR_ENA_W::new(self, 7)
    }
    #[doc = "Bit 8 - Core0 stackpoint underflow monitor enable"]
    #[inline(always)]
    pub fn sp_spill_min_ena(&mut self) -> SP_SPILL_MIN_ENA_W<'_, MONTR_ENA_SPEC> {
        SP_SPILL_MIN_ENA_W::new(self, 8)
    }
    #[doc = "Bit 9 - Core0 stackpoint overflow monitor enable"]
    #[inline(always)]
    pub fn sp_spill_max_ena(&mut self) -> SP_SPILL_MAX_ENA_W<'_, MONTR_ENA_SPEC> {
        SP_SPILL_MAX_ENA_W::new(self, 9)
    }
    #[doc = "Bit 10 - IBUS busy monitor enable"]
    #[inline(always)]
    pub fn iram0_exception_monitor_ena(
        &mut self,
    ) -> IRAM0_EXCEPTION_MONITOR_ENA_W<'_, MONTR_ENA_SPEC> {
        IRAM0_EXCEPTION_MONITOR_ENA_W::new(self, 10)
    }
    #[doc = "Bit 11 - DBUS busy monitor enbale"]
    #[inline(always)]
    pub fn dram0_exception_monitor_ena(
        &mut self,
    ) -> DRAM0_EXCEPTION_MONITOR_ENA_W<'_, MONTR_ENA_SPEC> {
        DRAM0_EXCEPTION_MONITOR_ENA_W::new(self, 11)
    }
}
#[doc = "ASSIST_DEBUG_CORE_0_MONTR_ENA_REG\n\nYou can [`read`](crate::Reg::read) this register and get [`montr_ena::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`montr_ena::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct MONTR_ENA_SPEC;
impl crate::RegisterSpec for MONTR_ENA_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`montr_ena::R`](R) reader structure"]
impl crate::Readable for MONTR_ENA_SPEC {}
#[doc = "`write(|w| ..)` method takes [`montr_ena::W`](W) writer structure"]
impl crate::Writable for MONTR_ENA_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets MONTR_ENA to value 0"]
impl crate::Resettable for MONTR_ENA_SPEC {}
