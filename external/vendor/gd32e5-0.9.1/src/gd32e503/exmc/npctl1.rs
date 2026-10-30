#[doc = "Register `NPCTL1` reader"]
pub type R = crate::R<Npctl1Spec>;
#[doc = "Register `NPCTL1` writer"]
pub type W = crate::W<Npctl1Spec>;
#[doc = "Field `NDWTEN` reader - Wait feature enable"]
pub type NdwtenR = crate::BitReader;
#[doc = "Field `NDWTEN` writer - Wait feature enable"]
pub type NdwtenW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `NDBKEN` reader - NAND bank enable"]
pub type NdbkenR = crate::BitReader;
#[doc = "Field `NDBKEN` writer - NAND bank enable"]
pub type NdbkenW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `NDTP` reader - NAND bank memory type"]
pub type NdtpR = crate::BitReader;
#[doc = "Field `NDTP` writer - NAND bank memory type"]
pub type NdtpW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `NDW` reader - NAND bank memory data bus width"]
pub type NdwR = crate::FieldReader;
#[doc = "Field `NDW` writer - NAND bank memory data bus width"]
pub type NdwW<'a, REG> = crate::FieldWriter<'a, REG, 2>;
#[doc = "Field `ECCEN` reader - ECC enable"]
pub type EccenR = crate::BitReader;
#[doc = "Field `ECCEN` writer - ECC enable"]
pub type EccenW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `CTR` reader - CLE to RE delay"]
pub type CtrR = crate::FieldReader;
#[doc = "Field `CTR` writer - CLE to RE delay"]
pub type CtrW<'a, REG> = crate::FieldWriter<'a, REG, 4>;
#[doc = "Field `ATR` reader - ALE to RE delay"]
pub type AtrR = crate::FieldReader;
#[doc = "Field `ATR` writer - ALE to RE delay"]
pub type AtrW<'a, REG> = crate::FieldWriter<'a, REG, 4>;
#[doc = "Field `ECCSZ` reader - ECC size"]
pub type EccszR = crate::FieldReader;
#[doc = "Field `ECCSZ` writer - ECC size"]
pub type EccszW<'a, REG> = crate::FieldWriter<'a, REG, 3>;
impl R {
    #[doc = "Bit 1 - Wait feature enable"]
    #[inline(always)]
    pub fn ndwten(&self) -> NdwtenR {
        NdwtenR::new(((self.bits >> 1) & 1) != 0)
    }
    #[doc = "Bit 2 - NAND bank enable"]
    #[inline(always)]
    pub fn ndbken(&self) -> NdbkenR {
        NdbkenR::new(((self.bits >> 2) & 1) != 0)
    }
    #[doc = "Bit 3 - NAND bank memory type"]
    #[inline(always)]
    pub fn ndtp(&self) -> NdtpR {
        NdtpR::new(((self.bits >> 3) & 1) != 0)
    }
    #[doc = "Bits 4:5 - NAND bank memory data bus width"]
    #[inline(always)]
    pub fn ndw(&self) -> NdwR {
        NdwR::new(((self.bits >> 4) & 3) as u8)
    }
    #[doc = "Bit 6 - ECC enable"]
    #[inline(always)]
    pub fn eccen(&self) -> EccenR {
        EccenR::new(((self.bits >> 6) & 1) != 0)
    }
    #[doc = "Bits 9:12 - CLE to RE delay"]
    #[inline(always)]
    pub fn ctr(&self) -> CtrR {
        CtrR::new(((self.bits >> 9) & 0x0f) as u8)
    }
    #[doc = "Bits 13:16 - ALE to RE delay"]
    #[inline(always)]
    pub fn atr(&self) -> AtrR {
        AtrR::new(((self.bits >> 13) & 0x0f) as u8)
    }
    #[doc = "Bits 17:19 - ECC size"]
    #[inline(always)]
    pub fn eccsz(&self) -> EccszR {
        EccszR::new(((self.bits >> 17) & 7) as u8)
    }
}
impl W {
    #[doc = "Bit 1 - Wait feature enable"]
    #[inline(always)]
    #[must_use]
    pub fn ndwten(&mut self) -> NdwtenW<Npctl1Spec> {
        NdwtenW::new(self, 1)
    }
    #[doc = "Bit 2 - NAND bank enable"]
    #[inline(always)]
    #[must_use]
    pub fn ndbken(&mut self) -> NdbkenW<Npctl1Spec> {
        NdbkenW::new(self, 2)
    }
    #[doc = "Bit 3 - NAND bank memory type"]
    #[inline(always)]
    #[must_use]
    pub fn ndtp(&mut self) -> NdtpW<Npctl1Spec> {
        NdtpW::new(self, 3)
    }
    #[doc = "Bits 4:5 - NAND bank memory data bus width"]
    #[inline(always)]
    #[must_use]
    pub fn ndw(&mut self) -> NdwW<Npctl1Spec> {
        NdwW::new(self, 4)
    }
    #[doc = "Bit 6 - ECC enable"]
    #[inline(always)]
    #[must_use]
    pub fn eccen(&mut self) -> EccenW<Npctl1Spec> {
        EccenW::new(self, 6)
    }
    #[doc = "Bits 9:12 - CLE to RE delay"]
    #[inline(always)]
    #[must_use]
    pub fn ctr(&mut self) -> CtrW<Npctl1Spec> {
        CtrW::new(self, 9)
    }
    #[doc = "Bits 13:16 - ALE to RE delay"]
    #[inline(always)]
    #[must_use]
    pub fn atr(&mut self) -> AtrW<Npctl1Spec> {
        AtrW::new(self, 13)
    }
    #[doc = "Bits 17:19 - ECC size"]
    #[inline(always)]
    #[must_use]
    pub fn eccsz(&mut self) -> EccszW<Npctl1Spec> {
        EccszW::new(self, 17)
    }
}
#[doc = "NAND flash/PC card control register 1\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`npctl1::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`npctl1::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct Npctl1Spec;
impl crate::RegisterSpec for Npctl1Spec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`npctl1::R`](R) reader structure"]
impl crate::Readable for Npctl1Spec {}
#[doc = "`write(|w| ..)` method takes [`npctl1::W`](W) writer structure"]
impl crate::Writable for Npctl1Spec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets NPCTL1 to value 0x18"]
impl crate::Resettable for Npctl1Spec {
    const RESET_VALUE: u32 = 0x18;
}
