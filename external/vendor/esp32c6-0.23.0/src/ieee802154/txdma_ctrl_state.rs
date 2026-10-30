#[doc = "Register `TXDMA_CTRL_STATE` reader"]
pub type R = crate::R<TXDMA_CTRL_STATE_SPEC>;
#[doc = "Register `TXDMA_CTRL_STATE` writer"]
pub type W = crate::W<TXDMA_CTRL_STATE_SPEC>;
#[doc = "Field `TXDMA_WATER_LEVEL` reader - "]
pub type TXDMA_WATER_LEVEL_R = crate::FieldReader;
#[doc = "Field `TXDMA_WATER_LEVEL` writer - "]
pub type TXDMA_WATER_LEVEL_W<'a, REG> = crate::FieldWriter<'a, REG, 3>;
#[doc = "Field `TXDMA_FILL_ENTRY` reader - "]
pub type TXDMA_FILL_ENTRY_R = crate::FieldReader;
#[doc = "Field `TXDMA_FILL_ENTRY` writer - "]
pub type TXDMA_FILL_ENTRY_W<'a, REG> = crate::FieldWriter<'a, REG, 3>;
#[doc = "Field `TXDMA_STATE` reader - "]
pub type TXDMA_STATE_R = crate::FieldReader;
#[doc = "Field `TXDMA_STATE` writer - "]
pub type TXDMA_STATE_W<'a, REG> = crate::FieldWriter<'a, REG, 5>;
#[doc = "Field `TXDMA_FETCH_BYTE_CNT` reader - "]
pub type TXDMA_FETCH_BYTE_CNT_R = crate::FieldReader;
#[doc = "Field `TXDMA_FETCH_BYTE_CNT` writer - "]
pub type TXDMA_FETCH_BYTE_CNT_W<'a, REG> = crate::FieldWriter<'a, REG, 7>;
impl R {
    #[doc = "Bits 0:2"]
    #[inline(always)]
    pub fn txdma_water_level(&self) -> TXDMA_WATER_LEVEL_R {
        TXDMA_WATER_LEVEL_R::new((self.bits & 7) as u8)
    }
    #[doc = "Bits 4:6"]
    #[inline(always)]
    pub fn txdma_fill_entry(&self) -> TXDMA_FILL_ENTRY_R {
        TXDMA_FILL_ENTRY_R::new(((self.bits >> 4) & 7) as u8)
    }
    #[doc = "Bits 16:20"]
    #[inline(always)]
    pub fn txdma_state(&self) -> TXDMA_STATE_R {
        TXDMA_STATE_R::new(((self.bits >> 16) & 0x1f) as u8)
    }
    #[doc = "Bits 24:30"]
    #[inline(always)]
    pub fn txdma_fetch_byte_cnt(&self) -> TXDMA_FETCH_BYTE_CNT_R {
        TXDMA_FETCH_BYTE_CNT_R::new(((self.bits >> 24) & 0x7f) as u8)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("TXDMA_CTRL_STATE")
            .field("txdma_water_level", &self.txdma_water_level())
            .field("txdma_fill_entry", &self.txdma_fill_entry())
            .field("txdma_state", &self.txdma_state())
            .field("txdma_fetch_byte_cnt", &self.txdma_fetch_byte_cnt())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:2"]
    #[inline(always)]
    pub fn txdma_water_level(&mut self) -> TXDMA_WATER_LEVEL_W<'_, TXDMA_CTRL_STATE_SPEC> {
        TXDMA_WATER_LEVEL_W::new(self, 0)
    }
    #[doc = "Bits 4:6"]
    #[inline(always)]
    pub fn txdma_fill_entry(&mut self) -> TXDMA_FILL_ENTRY_W<'_, TXDMA_CTRL_STATE_SPEC> {
        TXDMA_FILL_ENTRY_W::new(self, 4)
    }
    #[doc = "Bits 16:20"]
    #[inline(always)]
    pub fn txdma_state(&mut self) -> TXDMA_STATE_W<'_, TXDMA_CTRL_STATE_SPEC> {
        TXDMA_STATE_W::new(self, 16)
    }
    #[doc = "Bits 24:30"]
    #[inline(always)]
    pub fn txdma_fetch_byte_cnt(&mut self) -> TXDMA_FETCH_BYTE_CNT_W<'_, TXDMA_CTRL_STATE_SPEC> {
        TXDMA_FETCH_BYTE_CNT_W::new(self, 24)
    }
}
#[doc = "\n\nYou can [`read`](crate::Reg::read) this register and get [`txdma_ctrl_state::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`txdma_ctrl_state::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct TXDMA_CTRL_STATE_SPEC;
impl crate::RegisterSpec for TXDMA_CTRL_STATE_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`txdma_ctrl_state::R`](R) reader structure"]
impl crate::Readable for TXDMA_CTRL_STATE_SPEC {}
#[doc = "`write(|w| ..)` method takes [`txdma_ctrl_state::W`](W) writer structure"]
impl crate::Writable for TXDMA_CTRL_STATE_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets TXDMA_CTRL_STATE to value 0"]
impl crate::Resettable for TXDMA_CTRL_STATE_SPEC {}
