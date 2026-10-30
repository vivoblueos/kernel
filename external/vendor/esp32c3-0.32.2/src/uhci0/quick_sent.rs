#[doc = "Register `QUICK_SENT` reader"]
pub type R = crate::R<QUICK_SENT_SPEC>;
#[doc = "Register `QUICK_SENT` writer"]
pub type W = crate::W<QUICK_SENT_SPEC>;
#[doc = "Field `SINGLE_SEND_NUM` reader - a"]
pub type SINGLE_SEND_NUM_R = crate::FieldReader;
#[doc = "Field `SINGLE_SEND_NUM` writer - a"]
pub type SINGLE_SEND_NUM_W<'a, REG> = crate::FieldWriter<'a, REG, 3>;
#[doc = "Field `SINGLE_SEND_EN` reader - a"]
pub type SINGLE_SEND_EN_R = crate::BitReader;
#[doc = "Field `SINGLE_SEND_EN` writer - a"]
pub type SINGLE_SEND_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ALWAYS_SEND_NUM` reader - a"]
pub type ALWAYS_SEND_NUM_R = crate::FieldReader;
#[doc = "Field `ALWAYS_SEND_NUM` writer - a"]
pub type ALWAYS_SEND_NUM_W<'a, REG> = crate::FieldWriter<'a, REG, 3>;
#[doc = "Field `ALWAYS_SEND_EN` reader - a"]
pub type ALWAYS_SEND_EN_R = crate::BitReader;
#[doc = "Field `ALWAYS_SEND_EN` writer - a"]
pub type ALWAYS_SEND_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bits 0:2 - a"]
    #[inline(always)]
    pub fn single_send_num(&self) -> SINGLE_SEND_NUM_R {
        SINGLE_SEND_NUM_R::new((self.bits & 7) as u8)
    }
    #[doc = "Bit 3 - a"]
    #[inline(always)]
    pub fn single_send_en(&self) -> SINGLE_SEND_EN_R {
        SINGLE_SEND_EN_R::new(((self.bits >> 3) & 1) != 0)
    }
    #[doc = "Bits 4:6 - a"]
    #[inline(always)]
    pub fn always_send_num(&self) -> ALWAYS_SEND_NUM_R {
        ALWAYS_SEND_NUM_R::new(((self.bits >> 4) & 7) as u8)
    }
    #[doc = "Bit 7 - a"]
    #[inline(always)]
    pub fn always_send_en(&self) -> ALWAYS_SEND_EN_R {
        ALWAYS_SEND_EN_R::new(((self.bits >> 7) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("QUICK_SENT")
            .field("single_send_num", &self.single_send_num())
            .field("single_send_en", &self.single_send_en())
            .field("always_send_num", &self.always_send_num())
            .field("always_send_en", &self.always_send_en())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:2 - a"]
    #[inline(always)]
    pub fn single_send_num(&mut self) -> SINGLE_SEND_NUM_W<'_, QUICK_SENT_SPEC> {
        SINGLE_SEND_NUM_W::new(self, 0)
    }
    #[doc = "Bit 3 - a"]
    #[inline(always)]
    pub fn single_send_en(&mut self) -> SINGLE_SEND_EN_W<'_, QUICK_SENT_SPEC> {
        SINGLE_SEND_EN_W::new(self, 3)
    }
    #[doc = "Bits 4:6 - a"]
    #[inline(always)]
    pub fn always_send_num(&mut self) -> ALWAYS_SEND_NUM_W<'_, QUICK_SENT_SPEC> {
        ALWAYS_SEND_NUM_W::new(self, 4)
    }
    #[doc = "Bit 7 - a"]
    #[inline(always)]
    pub fn always_send_en(&mut self) -> ALWAYS_SEND_EN_W<'_, QUICK_SENT_SPEC> {
        ALWAYS_SEND_EN_W::new(self, 7)
    }
}
#[doc = "a\n\nYou can [`read`](crate::Reg::read) this register and get [`quick_sent::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`quick_sent::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct QUICK_SENT_SPEC;
impl crate::RegisterSpec for QUICK_SENT_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`quick_sent::R`](R) reader structure"]
impl crate::Readable for QUICK_SENT_SPEC {}
#[doc = "`write(|w| ..)` method takes [`quick_sent::W`](W) writer structure"]
impl crate::Writable for QUICK_SENT_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets QUICK_SENT to value 0"]
impl crate::Resettable for QUICK_SENT_SPEC {}
