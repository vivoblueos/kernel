#[doc = "Register `GLPMCFG` reader"]
pub type R = crate::R<GlpmcfgSpec>;
#[doc = "Register `GLPMCFG` writer"]
pub type W = crate::W<GlpmcfgSpec>;
#[doc = "Field `LPMEN` reader - LPM enable"]
pub type LpmenR = crate::BitReader;
#[doc = "Field `LPMEN` writer - LPM enable"]
pub type LpmenW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ACKLPM` reader - ACK in LPM transaction enable"]
pub type AcklpmR = crate::BitReader;
#[doc = "Field `ACKLPM` writer - ACK in LPM transaction enable"]
pub type AcklpmW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `BESL` reader - Best effort service latency"]
pub type BeslR = crate::FieldReader;
#[doc = "Field `BESL` writer - Best effort service latency"]
pub type BeslW<'a, REG> = crate::FieldWriter<'a, REG, 4>;
#[doc = "Field `REW` reader - RemoteWake value"]
pub type RewR = crate::BitReader;
#[doc = "Field `REW` writer - RemoteWake value"]
pub type RewW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SSEN` reader - Shallow sleep enable"]
pub type SsenR = crate::BitReader;
#[doc = "Field `SSEN` writer - Shallow sleep enable"]
pub type SsenW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `BESLTH` reader - BESL threshold"]
pub type BeslthR = crate::FieldReader;
#[doc = "Field `BESLTH` writer - BESL threshold"]
pub type BeslthW<'a, REG> = crate::FieldWriter<'a, REG, 4>;
#[doc = "Field `DSEN` reader - Deep sleep enable"]
pub type DsenR = crate::BitReader;
#[doc = "Field `DSEN` writer - Deep sleep enable"]
pub type DsenW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `LPMRSP` reader - Response of LPM"]
pub type LpmrspR = crate::FieldReader;
#[doc = "Field `LPMRSP` writer - Response of LPM"]
pub type LpmrspW<'a, REG> = crate::FieldWriter<'a, REG, 2>;
#[doc = "Field `LPMSLPS` reader - Sleep status"]
pub type LpmslpsR = crate::BitReader;
#[doc = "Field `LPMSLPS` writer - Sleep status"]
pub type LpmslpsW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `RSOK` reader - Resume can be sent after sleep state"]
pub type RsokR = crate::BitReader;
#[doc = "Field `RSOK` writer - Resume can be sent after sleep state"]
pub type RsokW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `LPMCHI` reader - Channel number index when send LPM transaction"]
pub type LpmchiR = crate::FieldReader;
#[doc = "Field `LPMCHI` writer - Channel number index when send LPM transaction"]
pub type LpmchiW<'a, REG> = crate::FieldWriter<'a, REG, 4>;
#[doc = "Field `LPMRC` reader - LPM retry count"]
pub type LpmrcR = crate::FieldReader;
#[doc = "Field `LPMRC` writer - LPM retry count"]
pub type LpmrcW<'a, REG> = crate::FieldWriter<'a, REG, 3>;
#[doc = "Field `LPMSND` reader - Send LPM transaction"]
pub type LpmsndR = crate::BitReader;
#[doc = "Field `LPMSND` writer - Send LPM transaction"]
pub type LpmsndW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `LPMRCS` reader - LPM retry count status"]
pub type LpmrcsR = crate::FieldReader;
#[doc = "Field `LPMRCS` writer - LPM retry count status"]
pub type LpmrcsW<'a, REG> = crate::FieldWriter<'a, REG, 3>;
#[doc = "Field `BESLEN` reader - LPM Errata selection enable"]
pub type BeslenR = crate::BitReader;
#[doc = "Field `BESLEN` writer - LPM Errata selection enable"]
pub type BeslenW<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 0 - LPM enable"]
    #[inline(always)]
    pub fn lpmen(&self) -> LpmenR {
        LpmenR::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - ACK in LPM transaction enable"]
    #[inline(always)]
    pub fn acklpm(&self) -> AcklpmR {
        AcklpmR::new(((self.bits >> 1) & 1) != 0)
    }
    #[doc = "Bits 2:5 - Best effort service latency"]
    #[inline(always)]
    pub fn besl(&self) -> BeslR {
        BeslR::new(((self.bits >> 2) & 0x0f) as u8)
    }
    #[doc = "Bit 6 - RemoteWake value"]
    #[inline(always)]
    pub fn rew(&self) -> RewR {
        RewR::new(((self.bits >> 6) & 1) != 0)
    }
    #[doc = "Bit 7 - Shallow sleep enable"]
    #[inline(always)]
    pub fn ssen(&self) -> SsenR {
        SsenR::new(((self.bits >> 7) & 1) != 0)
    }
    #[doc = "Bits 8:11 - BESL threshold"]
    #[inline(always)]
    pub fn beslth(&self) -> BeslthR {
        BeslthR::new(((self.bits >> 8) & 0x0f) as u8)
    }
    #[doc = "Bit 12 - Deep sleep enable"]
    #[inline(always)]
    pub fn dsen(&self) -> DsenR {
        DsenR::new(((self.bits >> 12) & 1) != 0)
    }
    #[doc = "Bits 13:14 - Response of LPM"]
    #[inline(always)]
    pub fn lpmrsp(&self) -> LpmrspR {
        LpmrspR::new(((self.bits >> 13) & 3) as u8)
    }
    #[doc = "Bit 15 - Sleep status"]
    #[inline(always)]
    pub fn lpmslps(&self) -> LpmslpsR {
        LpmslpsR::new(((self.bits >> 15) & 1) != 0)
    }
    #[doc = "Bit 16 - Resume can be sent after sleep state"]
    #[inline(always)]
    pub fn rsok(&self) -> RsokR {
        RsokR::new(((self.bits >> 16) & 1) != 0)
    }
    #[doc = "Bits 17:20 - Channel number index when send LPM transaction"]
    #[inline(always)]
    pub fn lpmchi(&self) -> LpmchiR {
        LpmchiR::new(((self.bits >> 17) & 0x0f) as u8)
    }
    #[doc = "Bits 21:23 - LPM retry count"]
    #[inline(always)]
    pub fn lpmrc(&self) -> LpmrcR {
        LpmrcR::new(((self.bits >> 21) & 7) as u8)
    }
    #[doc = "Bit 24 - Send LPM transaction"]
    #[inline(always)]
    pub fn lpmsnd(&self) -> LpmsndR {
        LpmsndR::new(((self.bits >> 24) & 1) != 0)
    }
    #[doc = "Bits 25:27 - LPM retry count status"]
    #[inline(always)]
    pub fn lpmrcs(&self) -> LpmrcsR {
        LpmrcsR::new(((self.bits >> 25) & 7) as u8)
    }
    #[doc = "Bit 28 - LPM Errata selection enable"]
    #[inline(always)]
    pub fn beslen(&self) -> BeslenR {
        BeslenR::new(((self.bits >> 28) & 1) != 0)
    }
}
impl W {
    #[doc = "Bit 0 - LPM enable"]
    #[inline(always)]
    #[must_use]
    pub fn lpmen(&mut self) -> LpmenW<GlpmcfgSpec> {
        LpmenW::new(self, 0)
    }
    #[doc = "Bit 1 - ACK in LPM transaction enable"]
    #[inline(always)]
    #[must_use]
    pub fn acklpm(&mut self) -> AcklpmW<GlpmcfgSpec> {
        AcklpmW::new(self, 1)
    }
    #[doc = "Bits 2:5 - Best effort service latency"]
    #[inline(always)]
    #[must_use]
    pub fn besl(&mut self) -> BeslW<GlpmcfgSpec> {
        BeslW::new(self, 2)
    }
    #[doc = "Bit 6 - RemoteWake value"]
    #[inline(always)]
    #[must_use]
    pub fn rew(&mut self) -> RewW<GlpmcfgSpec> {
        RewW::new(self, 6)
    }
    #[doc = "Bit 7 - Shallow sleep enable"]
    #[inline(always)]
    #[must_use]
    pub fn ssen(&mut self) -> SsenW<GlpmcfgSpec> {
        SsenW::new(self, 7)
    }
    #[doc = "Bits 8:11 - BESL threshold"]
    #[inline(always)]
    #[must_use]
    pub fn beslth(&mut self) -> BeslthW<GlpmcfgSpec> {
        BeslthW::new(self, 8)
    }
    #[doc = "Bit 12 - Deep sleep enable"]
    #[inline(always)]
    #[must_use]
    pub fn dsen(&mut self) -> DsenW<GlpmcfgSpec> {
        DsenW::new(self, 12)
    }
    #[doc = "Bits 13:14 - Response of LPM"]
    #[inline(always)]
    #[must_use]
    pub fn lpmrsp(&mut self) -> LpmrspW<GlpmcfgSpec> {
        LpmrspW::new(self, 13)
    }
    #[doc = "Bit 15 - Sleep status"]
    #[inline(always)]
    #[must_use]
    pub fn lpmslps(&mut self) -> LpmslpsW<GlpmcfgSpec> {
        LpmslpsW::new(self, 15)
    }
    #[doc = "Bit 16 - Resume can be sent after sleep state"]
    #[inline(always)]
    #[must_use]
    pub fn rsok(&mut self) -> RsokW<GlpmcfgSpec> {
        RsokW::new(self, 16)
    }
    #[doc = "Bits 17:20 - Channel number index when send LPM transaction"]
    #[inline(always)]
    #[must_use]
    pub fn lpmchi(&mut self) -> LpmchiW<GlpmcfgSpec> {
        LpmchiW::new(self, 17)
    }
    #[doc = "Bits 21:23 - LPM retry count"]
    #[inline(always)]
    #[must_use]
    pub fn lpmrc(&mut self) -> LpmrcW<GlpmcfgSpec> {
        LpmrcW::new(self, 21)
    }
    #[doc = "Bit 24 - Send LPM transaction"]
    #[inline(always)]
    #[must_use]
    pub fn lpmsnd(&mut self) -> LpmsndW<GlpmcfgSpec> {
        LpmsndW::new(self, 24)
    }
    #[doc = "Bits 25:27 - LPM retry count status"]
    #[inline(always)]
    #[must_use]
    pub fn lpmrcs(&mut self) -> LpmrcsW<GlpmcfgSpec> {
        LpmrcsW::new(self, 25)
    }
    #[doc = "Bit 28 - LPM Errata selection enable"]
    #[inline(always)]
    #[must_use]
    pub fn beslen(&mut self) -> BeslenW<GlpmcfgSpec> {
        BeslenW::new(self, 28)
    }
}
#[doc = "Global core LPM configuration register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`glpmcfg::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`glpmcfg::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct GlpmcfgSpec;
impl crate::RegisterSpec for GlpmcfgSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`glpmcfg::R`](R) reader structure"]
impl crate::Readable for GlpmcfgSpec {}
#[doc = "`write(|w| ..)` method takes [`glpmcfg::W`](W) writer structure"]
impl crate::Writable for GlpmcfgSpec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets GLPMCFG to value 0"]
impl crate::Resettable for GlpmcfgSpec {
    const RESET_VALUE: u32 = 0;
}
