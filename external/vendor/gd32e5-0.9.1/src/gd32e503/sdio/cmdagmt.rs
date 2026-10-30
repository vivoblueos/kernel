#[doc = "Register `CMDAGMT` reader"]
pub type R = crate::R<CmdagmtSpec>;
#[doc = "Register `CMDAGMT` writer"]
pub type W = crate::W<CmdagmtSpec>;
#[doc = "Field `CMDAGMT` reader - SDIO card command argument"]
pub type CmdagmtR = crate::FieldReader<u32>;
#[doc = "Field `CMDAGMT` writer - SDIO card command argument"]
pub type CmdagmtW<'a, REG> = crate::FieldWriter<'a, REG, 32, u32>;
impl R {
    #[doc = "Bits 0:31 - SDIO card command argument"]
    #[inline(always)]
    pub fn cmdagmt(&self) -> CmdagmtR {
        CmdagmtR::new(self.bits)
    }
}
impl W {
    #[doc = "Bits 0:31 - SDIO card command argument"]
    #[inline(always)]
    #[must_use]
    pub fn cmdagmt(&mut self) -> CmdagmtW<CmdagmtSpec> {
        CmdagmtW::new(self, 0)
    }
}
#[doc = "Command argument register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`cmdagmt::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`cmdagmt::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct CmdagmtSpec;
impl crate::RegisterSpec for CmdagmtSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`cmdagmt::R`](R) reader structure"]
impl crate::Readable for CmdagmtSpec {}
#[doc = "`write(|w| ..)` method takes [`cmdagmt::W`](W) writer structure"]
impl crate::Writable for CmdagmtSpec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets CMDAGMT to value 0"]
impl crate::Resettable for CmdagmtSpec {
    const RESET_VALUE: u32 = 0;
}
