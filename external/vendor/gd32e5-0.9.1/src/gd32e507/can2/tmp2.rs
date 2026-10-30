#[doc = "Register `TMP2` reader"]
pub type R = crate::R<Tmp2Spec>;
#[doc = "Register `TMP2` writer"]
pub type W = crate::W<Tmp2Spec>;
#[doc = "Field `DLENC` reader - Data length code"]
pub type DlencR = crate::FieldReader;
#[doc = "Field `DLENC` writer - Data length code"]
pub type DlencW<'a, REG> = crate::FieldWriter<'a, REG, 4>;
#[doc = "Field `ESI` reader - Error status indicator"]
pub type EsiR = crate::BitReader;
#[doc = "Field `ESI` writer - Error status indicator"]
pub type EsiW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `BRS` reader - Bit rate of data switch"]
pub type BrsR = crate::BitReader;
#[doc = "Field `BRS` writer - Bit rate of data switch"]
pub type BrsW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `FDF` reader - CAN FD frame flag"]
pub type FdfR = crate::BitReader;
#[doc = "Field `FDF` writer - CAN FD frame flag"]
pub type FdfW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `TSEN` reader - Time stamp enable"]
pub type TsenR = crate::BitReader;
#[doc = "Field `TSEN` writer - Time stamp enable"]
pub type TsenW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `TS` reader - Time stamp"]
pub type TsR = crate::FieldReader<u16>;
#[doc = "Field `TS` writer - Time stamp"]
pub type TsW<'a, REG> = crate::FieldWriter<'a, REG, 16, u16>;
impl R {
    #[doc = "Bits 0:3 - Data length code"]
    #[inline(always)]
    pub fn dlenc(&self) -> DlencR {
        DlencR::new((self.bits & 0x0f) as u8)
    }
    #[doc = "Bit 4 - Error status indicator"]
    #[inline(always)]
    pub fn esi(&self) -> EsiR {
        EsiR::new(((self.bits >> 4) & 1) != 0)
    }
    #[doc = "Bit 5 - Bit rate of data switch"]
    #[inline(always)]
    pub fn brs(&self) -> BrsR {
        BrsR::new(((self.bits >> 5) & 1) != 0)
    }
    #[doc = "Bit 7 - CAN FD frame flag"]
    #[inline(always)]
    pub fn fdf(&self) -> FdfR {
        FdfR::new(((self.bits >> 7) & 1) != 0)
    }
    #[doc = "Bit 8 - Time stamp enable"]
    #[inline(always)]
    pub fn tsen(&self) -> TsenR {
        TsenR::new(((self.bits >> 8) & 1) != 0)
    }
    #[doc = "Bits 16:31 - Time stamp"]
    #[inline(always)]
    pub fn ts(&self) -> TsR {
        TsR::new(((self.bits >> 16) & 0xffff) as u16)
    }
}
impl W {
    #[doc = "Bits 0:3 - Data length code"]
    #[inline(always)]
    #[must_use]
    pub fn dlenc(&mut self) -> DlencW<Tmp2Spec> {
        DlencW::new(self, 0)
    }
    #[doc = "Bit 4 - Error status indicator"]
    #[inline(always)]
    #[must_use]
    pub fn esi(&mut self) -> EsiW<Tmp2Spec> {
        EsiW::new(self, 4)
    }
    #[doc = "Bit 5 - Bit rate of data switch"]
    #[inline(always)]
    #[must_use]
    pub fn brs(&mut self) -> BrsW<Tmp2Spec> {
        BrsW::new(self, 5)
    }
    #[doc = "Bit 7 - CAN FD frame flag"]
    #[inline(always)]
    #[must_use]
    pub fn fdf(&mut self) -> FdfW<Tmp2Spec> {
        FdfW::new(self, 7)
    }
    #[doc = "Bit 8 - Time stamp enable"]
    #[inline(always)]
    #[must_use]
    pub fn tsen(&mut self) -> TsenW<Tmp2Spec> {
        TsenW::new(self, 8)
    }
    #[doc = "Bits 16:31 - Time stamp"]
    #[inline(always)]
    #[must_use]
    pub fn ts(&mut self) -> TsW<Tmp2Spec> {
        TsW::new(self, 16)
    }
}
#[doc = "Transmit mailbox property register 2\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`tmp2::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`tmp2::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct Tmp2Spec;
impl crate::RegisterSpec for Tmp2Spec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`tmp2::R`](R) reader structure"]
impl crate::Readable for Tmp2Spec {}
#[doc = "`write(|w| ..)` method takes [`tmp2::W`](W) writer structure"]
impl crate::Writable for Tmp2Spec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets TMP2 to value 0"]
impl crate::Resettable for Tmp2Spec {
    const RESET_VALUE: u32 = 0;
}
