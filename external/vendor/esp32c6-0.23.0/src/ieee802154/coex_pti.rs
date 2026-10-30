#[doc = "Register `COEX_PTI` reader"]
pub type R = crate::R<COEX_PTI_SPEC>;
#[doc = "Register `COEX_PTI` writer"]
pub type W = crate::W<COEX_PTI_SPEC>;
#[doc = "Field `COEX_PTI` reader - "]
pub type COEX_PTI_R = crate::FieldReader;
#[doc = "Field `COEX_PTI` writer - "]
pub type COEX_PTI_W<'a, REG> = crate::FieldWriter<'a, REG, 4>;
#[doc = "Field `COEX_ACK_PTI` reader - "]
pub type COEX_ACK_PTI_R = crate::FieldReader;
#[doc = "Field `COEX_ACK_PTI` writer - "]
pub type COEX_ACK_PTI_W<'a, REG> = crate::FieldWriter<'a, REG, 4>;
#[doc = "Field `CLOSE_RF_SEL` reader - "]
pub type CLOSE_RF_SEL_R = crate::BitReader;
#[doc = "Field `CLOSE_RF_SEL` writer - "]
pub type CLOSE_RF_SEL_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bits 0:3"]
    #[inline(always)]
    pub fn coex_pti(&self) -> COEX_PTI_R {
        COEX_PTI_R::new((self.bits & 0x0f) as u8)
    }
    #[doc = "Bits 4:7"]
    #[inline(always)]
    pub fn coex_ack_pti(&self) -> COEX_ACK_PTI_R {
        COEX_ACK_PTI_R::new(((self.bits >> 4) & 0x0f) as u8)
    }
    #[doc = "Bit 8"]
    #[inline(always)]
    pub fn close_rf_sel(&self) -> CLOSE_RF_SEL_R {
        CLOSE_RF_SEL_R::new(((self.bits >> 8) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("COEX_PTI")
            .field("coex_pti", &self.coex_pti())
            .field("coex_ack_pti", &self.coex_ack_pti())
            .field("close_rf_sel", &self.close_rf_sel())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:3"]
    #[inline(always)]
    pub fn coex_pti(&mut self) -> COEX_PTI_W<'_, COEX_PTI_SPEC> {
        COEX_PTI_W::new(self, 0)
    }
    #[doc = "Bits 4:7"]
    #[inline(always)]
    pub fn coex_ack_pti(&mut self) -> COEX_ACK_PTI_W<'_, COEX_PTI_SPEC> {
        COEX_ACK_PTI_W::new(self, 4)
    }
    #[doc = "Bit 8"]
    #[inline(always)]
    pub fn close_rf_sel(&mut self) -> CLOSE_RF_SEL_W<'_, COEX_PTI_SPEC> {
        CLOSE_RF_SEL_W::new(self, 8)
    }
}
#[doc = "\n\nYou can [`read`](crate::Reg::read) this register and get [`coex_pti::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`coex_pti::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct COEX_PTI_SPEC;
impl crate::RegisterSpec for COEX_PTI_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`coex_pti::R`](R) reader structure"]
impl crate::Readable for COEX_PTI_SPEC {}
#[doc = "`write(|w| ..)` method takes [`coex_pti::W`](W) writer structure"]
impl crate::Writable for COEX_PTI_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets COEX_PTI to value 0"]
impl crate::Resettable for COEX_PTI_SPEC {}
