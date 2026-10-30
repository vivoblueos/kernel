#[doc = "Register `ICACHE_AUTOLOAD_CTRL` reader"]
pub type R = crate::R<ICACHE_AUTOLOAD_CTRL_SPEC>;
#[doc = "Register `ICACHE_AUTOLOAD_CTRL` writer"]
pub type W = crate::W<ICACHE_AUTOLOAD_CTRL_SPEC>;
#[doc = "Field `ICACHE_AUTOLOAD_SCT0_ENA` reader - The bits are used to enable the first section for autoload operation."]
pub type ICACHE_AUTOLOAD_SCT0_ENA_R = crate::BitReader;
#[doc = "Field `ICACHE_AUTOLOAD_SCT0_ENA` writer - The bits are used to enable the first section for autoload operation."]
pub type ICACHE_AUTOLOAD_SCT0_ENA_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ICACHE_AUTOLOAD_SCT1_ENA` reader - The bits are used to enable the second section for autoload operation."]
pub type ICACHE_AUTOLOAD_SCT1_ENA_R = crate::BitReader;
#[doc = "Field `ICACHE_AUTOLOAD_SCT1_ENA` writer - The bits are used to enable the second section for autoload operation."]
pub type ICACHE_AUTOLOAD_SCT1_ENA_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ICACHE_AUTOLOAD_ENA` reader - The bit is used to enable and disable autoload operation. It is combined with icache_autoload_done. 1: enable, 0: disable."]
pub type ICACHE_AUTOLOAD_ENA_R = crate::BitReader;
#[doc = "Field `ICACHE_AUTOLOAD_ENA` writer - The bit is used to enable and disable autoload operation. It is combined with icache_autoload_done. 1: enable, 0: disable."]
pub type ICACHE_AUTOLOAD_ENA_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ICACHE_AUTOLOAD_DONE` reader - The bit is used to indicate autoload operation is finished."]
pub type ICACHE_AUTOLOAD_DONE_R = crate::BitReader;
#[doc = "Field `ICACHE_AUTOLOAD_ORDER` reader - The bits are used to configure the direction of autoload. 1: descending, 0: ascending."]
pub type ICACHE_AUTOLOAD_ORDER_R = crate::BitReader;
#[doc = "Field `ICACHE_AUTOLOAD_ORDER` writer - The bits are used to configure the direction of autoload. 1: descending, 0: ascending."]
pub type ICACHE_AUTOLOAD_ORDER_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ICACHE_AUTOLOAD_RQST` reader - The bits are used to configure trigger conditions for autoload. 0/3: cache miss, 1: cache hit, 2: both cache miss and hit."]
pub type ICACHE_AUTOLOAD_RQST_R = crate::FieldReader;
#[doc = "Field `ICACHE_AUTOLOAD_RQST` writer - The bits are used to configure trigger conditions for autoload. 0/3: cache miss, 1: cache hit, 2: both cache miss and hit."]
pub type ICACHE_AUTOLOAD_RQST_W<'a, REG> = crate::FieldWriter<'a, REG, 2>;
impl R {
    #[doc = "Bit 0 - The bits are used to enable the first section for autoload operation."]
    #[inline(always)]
    pub fn icache_autoload_sct0_ena(&self) -> ICACHE_AUTOLOAD_SCT0_ENA_R {
        ICACHE_AUTOLOAD_SCT0_ENA_R::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - The bits are used to enable the second section for autoload operation."]
    #[inline(always)]
    pub fn icache_autoload_sct1_ena(&self) -> ICACHE_AUTOLOAD_SCT1_ENA_R {
        ICACHE_AUTOLOAD_SCT1_ENA_R::new(((self.bits >> 1) & 1) != 0)
    }
    #[doc = "Bit 2 - The bit is used to enable and disable autoload operation. It is combined with icache_autoload_done. 1: enable, 0: disable."]
    #[inline(always)]
    pub fn icache_autoload_ena(&self) -> ICACHE_AUTOLOAD_ENA_R {
        ICACHE_AUTOLOAD_ENA_R::new(((self.bits >> 2) & 1) != 0)
    }
    #[doc = "Bit 3 - The bit is used to indicate autoload operation is finished."]
    #[inline(always)]
    pub fn icache_autoload_done(&self) -> ICACHE_AUTOLOAD_DONE_R {
        ICACHE_AUTOLOAD_DONE_R::new(((self.bits >> 3) & 1) != 0)
    }
    #[doc = "Bit 4 - The bits are used to configure the direction of autoload. 1: descending, 0: ascending."]
    #[inline(always)]
    pub fn icache_autoload_order(&self) -> ICACHE_AUTOLOAD_ORDER_R {
        ICACHE_AUTOLOAD_ORDER_R::new(((self.bits >> 4) & 1) != 0)
    }
    #[doc = "Bits 5:6 - The bits are used to configure trigger conditions for autoload. 0/3: cache miss, 1: cache hit, 2: both cache miss and hit."]
    #[inline(always)]
    pub fn icache_autoload_rqst(&self) -> ICACHE_AUTOLOAD_RQST_R {
        ICACHE_AUTOLOAD_RQST_R::new(((self.bits >> 5) & 3) as u8)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("ICACHE_AUTOLOAD_CTRL")
            .field("icache_autoload_sct0_ena", &self.icache_autoload_sct0_ena())
            .field("icache_autoload_sct1_ena", &self.icache_autoload_sct1_ena())
            .field("icache_autoload_ena", &self.icache_autoload_ena())
            .field("icache_autoload_done", &self.icache_autoload_done())
            .field("icache_autoload_order", &self.icache_autoload_order())
            .field("icache_autoload_rqst", &self.icache_autoload_rqst())
            .finish()
    }
}
impl W {
    #[doc = "Bit 0 - The bits are used to enable the first section for autoload operation."]
    #[inline(always)]
    pub fn icache_autoload_sct0_ena(
        &mut self,
    ) -> ICACHE_AUTOLOAD_SCT0_ENA_W<'_, ICACHE_AUTOLOAD_CTRL_SPEC> {
        ICACHE_AUTOLOAD_SCT0_ENA_W::new(self, 0)
    }
    #[doc = "Bit 1 - The bits are used to enable the second section for autoload operation."]
    #[inline(always)]
    pub fn icache_autoload_sct1_ena(
        &mut self,
    ) -> ICACHE_AUTOLOAD_SCT1_ENA_W<'_, ICACHE_AUTOLOAD_CTRL_SPEC> {
        ICACHE_AUTOLOAD_SCT1_ENA_W::new(self, 1)
    }
    #[doc = "Bit 2 - The bit is used to enable and disable autoload operation. It is combined with icache_autoload_done. 1: enable, 0: disable."]
    #[inline(always)]
    pub fn icache_autoload_ena(&mut self) -> ICACHE_AUTOLOAD_ENA_W<'_, ICACHE_AUTOLOAD_CTRL_SPEC> {
        ICACHE_AUTOLOAD_ENA_W::new(self, 2)
    }
    #[doc = "Bit 4 - The bits are used to configure the direction of autoload. 1: descending, 0: ascending."]
    #[inline(always)]
    pub fn icache_autoload_order(
        &mut self,
    ) -> ICACHE_AUTOLOAD_ORDER_W<'_, ICACHE_AUTOLOAD_CTRL_SPEC> {
        ICACHE_AUTOLOAD_ORDER_W::new(self, 4)
    }
    #[doc = "Bits 5:6 - The bits are used to configure trigger conditions for autoload. 0/3: cache miss, 1: cache hit, 2: both cache miss and hit."]
    #[inline(always)]
    pub fn icache_autoload_rqst(
        &mut self,
    ) -> ICACHE_AUTOLOAD_RQST_W<'_, ICACHE_AUTOLOAD_CTRL_SPEC> {
        ICACHE_AUTOLOAD_RQST_W::new(self, 5)
    }
}
#[doc = "This description will be updated in the near future.\n\nYou can [`read`](crate::Reg::read) this register and get [`icache_autoload_ctrl::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`icache_autoload_ctrl::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct ICACHE_AUTOLOAD_CTRL_SPEC;
impl crate::RegisterSpec for ICACHE_AUTOLOAD_CTRL_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`icache_autoload_ctrl::R`](R) reader structure"]
impl crate::Readable for ICACHE_AUTOLOAD_CTRL_SPEC {}
#[doc = "`write(|w| ..)` method takes [`icache_autoload_ctrl::W`](W) writer structure"]
impl crate::Writable for ICACHE_AUTOLOAD_CTRL_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets ICACHE_AUTOLOAD_CTRL to value 0x08"]
impl crate::Resettable for ICACHE_AUTOLOAD_CTRL_SPEC {
    const RESET_VALUE: u32 = 0x08;
}
