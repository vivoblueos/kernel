#[doc = "Register `TMP1` reader"]
pub type R = crate::R<Tmp1Spec>;
#[doc = "Register `TMP1` writer"]
pub type W = crate::W<Tmp1Spec>;
#[doc = "Field `DLENC` reader - Data length code"]
pub type DlencR = crate::FieldReader;
#[doc = "Field `DLENC` writer - Data length code"]
pub type DlencW<'a, REG> = crate::FieldWriter<'a, REG, 4>;
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
    pub fn dlenc(&mut self) -> DlencW<Tmp1Spec> {
        DlencW::new(self, 0)
    }
    #[doc = "Bit 8 - Time stamp enable"]
    #[inline(always)]
    #[must_use]
    pub fn tsen(&mut self) -> TsenW<Tmp1Spec> {
        TsenW::new(self, 8)
    }
    #[doc = "Bits 16:31 - Time stamp"]
    #[inline(always)]
    #[must_use]
    pub fn ts(&mut self) -> TsW<Tmp1Spec> {
        TsW::new(self, 16)
    }
}
#[doc = "Transmit mailbox property register 1\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`tmp1::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`tmp1::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct Tmp1Spec;
impl crate::RegisterSpec for Tmp1Spec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`tmp1::R`](R) reader structure"]
impl crate::Readable for Tmp1Spec {}
#[doc = "`write(|w| ..)` method takes [`tmp1::W`](W) writer structure"]
impl crate::Writable for Tmp1Spec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets TMP1 to value 0"]
impl crate::Resettable for Tmp1Spec {
    const RESET_VALUE: u32 = 0;
}
