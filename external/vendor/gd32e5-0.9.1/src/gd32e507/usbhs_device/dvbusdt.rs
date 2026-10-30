#[doc = "Register `DVBUSDT` reader"]
pub type R = crate::R<DvbusdtSpec>;
#[doc = "Register `DVBUSDT` writer"]
pub type W = crate::W<DvbusdtSpec>;
#[doc = "Field `DVBUSDT` reader - Device VBUS discharge time"]
pub type DvbusdtR = crate::FieldReader<u16>;
#[doc = "Field `DVBUSDT` writer - Device VBUS discharge time"]
pub type DvbusdtW<'a, REG> = crate::FieldWriter<'a, REG, 16, u16>;
impl R {
    #[doc = "Bits 0:15 - Device VBUS discharge time"]
    #[inline(always)]
    pub fn dvbusdt(&self) -> DvbusdtR {
        DvbusdtR::new((self.bits & 0xffff) as u16)
    }
}
impl W {
    #[doc = "Bits 0:15 - Device VBUS discharge time"]
    #[inline(always)]
    #[must_use]
    pub fn dvbusdt(&mut self) -> DvbusdtW<DvbusdtSpec> {
        DvbusdtW::new(self, 0)
    }
}
#[doc = "device VBUS discharge time register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`dvbusdt::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`dvbusdt::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct DvbusdtSpec;
impl crate::RegisterSpec for DvbusdtSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`dvbusdt::R`](R) reader structure"]
impl crate::Readable for DvbusdtSpec {}
#[doc = "`write(|w| ..)` method takes [`dvbusdt::W`](W) writer structure"]
impl crate::Writable for DvbusdtSpec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets DVBUSDT to value 0x17d7"]
impl crate::Resettable for DvbusdtSpec {
    const RESET_VALUE: u32 = 0x17d7;
}
