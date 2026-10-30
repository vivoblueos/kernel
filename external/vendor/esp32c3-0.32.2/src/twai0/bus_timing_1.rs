#[doc = "Register `BUS_TIMING_1` reader"]
pub type R = crate::R<BUS_TIMING_1_SPEC>;
#[doc = "Register `BUS_TIMING_1` writer"]
pub type W = crate::W<BUS_TIMING_1_SPEC>;
#[doc = "Field `TIME_SEG1` reader - The width of PBS1."]
pub type TIME_SEG1_R = crate::FieldReader;
#[doc = "Field `TIME_SEG1` writer - The width of PBS1."]
pub type TIME_SEG1_W<'a, REG> = crate::FieldWriter<'a, REG, 4>;
#[doc = "Field `TIME_SEG2` reader - The width of PBS2."]
pub type TIME_SEG2_R = crate::FieldReader;
#[doc = "Field `TIME_SEG2` writer - The width of PBS2."]
pub type TIME_SEG2_W<'a, REG> = crate::FieldWriter<'a, REG, 3>;
#[doc = "Field `TIME_SAMP` reader - The number of sample points. 0: the bus is sampled once; 1: the bus is sampled three times"]
pub type TIME_SAMP_R = crate::BitReader;
#[doc = "Field `TIME_SAMP` writer - The number of sample points. 0: the bus is sampled once; 1: the bus is sampled three times"]
pub type TIME_SAMP_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bits 0:3 - The width of PBS1."]
    #[inline(always)]
    pub fn time_seg1(&self) -> TIME_SEG1_R {
        TIME_SEG1_R::new((self.bits & 0x0f) as u8)
    }
    #[doc = "Bits 4:6 - The width of PBS2."]
    #[inline(always)]
    pub fn time_seg2(&self) -> TIME_SEG2_R {
        TIME_SEG2_R::new(((self.bits >> 4) & 7) as u8)
    }
    #[doc = "Bit 7 - The number of sample points. 0: the bus is sampled once; 1: the bus is sampled three times"]
    #[inline(always)]
    pub fn time_samp(&self) -> TIME_SAMP_R {
        TIME_SAMP_R::new(((self.bits >> 7) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("BUS_TIMING_1")
            .field("time_seg1", &self.time_seg1())
            .field("time_seg2", &self.time_seg2())
            .field("time_samp", &self.time_samp())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:3 - The width of PBS1."]
    #[inline(always)]
    pub fn time_seg1(&mut self) -> TIME_SEG1_W<'_, BUS_TIMING_1_SPEC> {
        TIME_SEG1_W::new(self, 0)
    }
    #[doc = "Bits 4:6 - The width of PBS2."]
    #[inline(always)]
    pub fn time_seg2(&mut self) -> TIME_SEG2_W<'_, BUS_TIMING_1_SPEC> {
        TIME_SEG2_W::new(self, 4)
    }
    #[doc = "Bit 7 - The number of sample points. 0: the bus is sampled once; 1: the bus is sampled three times"]
    #[inline(always)]
    pub fn time_samp(&mut self) -> TIME_SAMP_W<'_, BUS_TIMING_1_SPEC> {
        TIME_SAMP_W::new(self, 7)
    }
}
#[doc = "Bus Timing Register 1\n\nYou can [`read`](crate::Reg::read) this register and get [`bus_timing_1::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`bus_timing_1::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct BUS_TIMING_1_SPEC;
impl crate::RegisterSpec for BUS_TIMING_1_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`bus_timing_1::R`](R) reader structure"]
impl crate::Readable for BUS_TIMING_1_SPEC {}
#[doc = "`write(|w| ..)` method takes [`bus_timing_1::W`](W) writer structure"]
impl crate::Writable for BUS_TIMING_1_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets BUS_TIMING_1 to value 0"]
impl crate::Resettable for BUS_TIMING_1_SPEC {}
