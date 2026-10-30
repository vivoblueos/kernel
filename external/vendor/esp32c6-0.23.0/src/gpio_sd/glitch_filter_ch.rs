#[doc = "Register `GLITCH_FILTER_CH%s` reader"]
pub type R = crate::R<GLITCH_FILTER_CH_SPEC>;
#[doc = "Register `GLITCH_FILTER_CH%s` writer"]
pub type W = crate::W<GLITCH_FILTER_CH_SPEC>;
#[doc = "Field `EN` reader - Glitch Filter channel enable bit."]
pub type EN_R = crate::BitReader;
#[doc = "Field `EN` writer - Glitch Filter channel enable bit."]
pub type EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `INPUT_IO_NUM` reader - Glitch Filter input io number."]
pub type INPUT_IO_NUM_R = crate::FieldReader;
#[doc = "Field `INPUT_IO_NUM` writer - Glitch Filter input io number."]
pub type INPUT_IO_NUM_W<'a, REG> = crate::FieldWriter<'a, REG, 6>;
#[doc = "Field `WINDOW_THRES` reader - Glitch Filter window threshold."]
pub type WINDOW_THRES_R = crate::FieldReader;
#[doc = "Field `WINDOW_THRES` writer - Glitch Filter window threshold."]
pub type WINDOW_THRES_W<'a, REG> = crate::FieldWriter<'a, REG, 6>;
#[doc = "Field `WINDOW_WIDTH` reader - Glitch Filter window width."]
pub type WINDOW_WIDTH_R = crate::FieldReader;
#[doc = "Field `WINDOW_WIDTH` writer - Glitch Filter window width."]
pub type WINDOW_WIDTH_W<'a, REG> = crate::FieldWriter<'a, REG, 6>;
impl R {
    #[doc = "Bit 0 - Glitch Filter channel enable bit."]
    #[inline(always)]
    pub fn en(&self) -> EN_R {
        EN_R::new((self.bits & 1) != 0)
    }
    #[doc = "Bits 1:6 - Glitch Filter input io number."]
    #[inline(always)]
    pub fn input_io_num(&self) -> INPUT_IO_NUM_R {
        INPUT_IO_NUM_R::new(((self.bits >> 1) & 0x3f) as u8)
    }
    #[doc = "Bits 7:12 - Glitch Filter window threshold."]
    #[inline(always)]
    pub fn window_thres(&self) -> WINDOW_THRES_R {
        WINDOW_THRES_R::new(((self.bits >> 7) & 0x3f) as u8)
    }
    #[doc = "Bits 13:18 - Glitch Filter window width."]
    #[inline(always)]
    pub fn window_width(&self) -> WINDOW_WIDTH_R {
        WINDOW_WIDTH_R::new(((self.bits >> 13) & 0x3f) as u8)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("GLITCH_FILTER_CH")
            .field("en", &self.en())
            .field("input_io_num", &self.input_io_num())
            .field("window_thres", &self.window_thres())
            .field("window_width", &self.window_width())
            .finish()
    }
}
impl W {
    #[doc = "Bit 0 - Glitch Filter channel enable bit."]
    #[inline(always)]
    pub fn en(&mut self) -> EN_W<'_, GLITCH_FILTER_CH_SPEC> {
        EN_W::new(self, 0)
    }
    #[doc = "Bits 1:6 - Glitch Filter input io number."]
    #[inline(always)]
    pub fn input_io_num(&mut self) -> INPUT_IO_NUM_W<'_, GLITCH_FILTER_CH_SPEC> {
        INPUT_IO_NUM_W::new(self, 1)
    }
    #[doc = "Bits 7:12 - Glitch Filter window threshold."]
    #[inline(always)]
    pub fn window_thres(&mut self) -> WINDOW_THRES_W<'_, GLITCH_FILTER_CH_SPEC> {
        WINDOW_THRES_W::new(self, 7)
    }
    #[doc = "Bits 13:18 - Glitch Filter window width."]
    #[inline(always)]
    pub fn window_width(&mut self) -> WINDOW_WIDTH_W<'_, GLITCH_FILTER_CH_SPEC> {
        WINDOW_WIDTH_W::new(self, 13)
    }
}
#[doc = "Glitch Filter Configure Register of Channel%s\n\nYou can [`read`](crate::Reg::read) this register and get [`glitch_filter_ch::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`glitch_filter_ch::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct GLITCH_FILTER_CH_SPEC;
impl crate::RegisterSpec for GLITCH_FILTER_CH_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`glitch_filter_ch::R`](R) reader structure"]
impl crate::Readable for GLITCH_FILTER_CH_SPEC {}
#[doc = "`write(|w| ..)` method takes [`glitch_filter_ch::W`](W) writer structure"]
impl crate::Writable for GLITCH_FILTER_CH_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets GLITCH_FILTER_CH%s to value 0"]
impl crate::Resettable for GLITCH_FILTER_CH_SPEC {}
