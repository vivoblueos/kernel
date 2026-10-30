#[doc = "Register `CFG_UHS1_INT_MODE` reader"]
pub type R = crate::R<CFG_UHS1_INT_MODE_SPEC>;
#[doc = "Register `CFG_UHS1_INT_MODE` writer"]
pub type W = crate::W<CFG_UHS1_INT_MODE_SPEC>;
#[doc = "Field `INTOE_END_AHEAD_MODE` reader - intoe on dat1 end ahead of time: 0/3-no, 1-ahead 1sdclk, 2-ahead 2sdclk"]
pub type INTOE_END_AHEAD_MODE_R = crate::FieldReader;
#[doc = "Field `INTOE_END_AHEAD_MODE` writer - intoe on dat1 end ahead of time: 0/3-no, 1-ahead 1sdclk, 2-ahead 2sdclk"]
pub type INTOE_END_AHEAD_MODE_W<'a, REG> = crate::FieldWriter<'a, REG, 2>;
#[doc = "Field `INT_END_AHEAD_MODE` reader - int on dat1 end ahead of time: 0/3-no, 1-ahead 1sdclk, 2-ahead 2sdclk"]
pub type INT_END_AHEAD_MODE_R = crate::FieldReader;
#[doc = "Field `INT_END_AHEAD_MODE` writer - int on dat1 end ahead of time: 0/3-no, 1-ahead 1sdclk, 2-ahead 2sdclk"]
pub type INT_END_AHEAD_MODE_W<'a, REG> = crate::FieldWriter<'a, REG, 2>;
#[doc = "Field `INTOE_ST_AHEAD_MODE` reader - intoe on dat1 start ahead of time: 0/3-no, 1-ahead 1sdclk, 2-ahead 2sdclk"]
pub type INTOE_ST_AHEAD_MODE_R = crate::FieldReader;
#[doc = "Field `INTOE_ST_AHEAD_MODE` writer - intoe on dat1 start ahead of time: 0/3-no, 1-ahead 1sdclk, 2-ahead 2sdclk"]
pub type INTOE_ST_AHEAD_MODE_W<'a, REG> = crate::FieldWriter<'a, REG, 2>;
#[doc = "Field `INT_ST_AHEAD_MODE` reader - int on dat1 start ahead of time: 0/3-no, 1-ahead 1sdclk, 2-ahead 2sdclk"]
pub type INT_ST_AHEAD_MODE_R = crate::FieldReader;
#[doc = "Field `INT_ST_AHEAD_MODE` writer - int on dat1 start ahead of time: 0/3-no, 1-ahead 1sdclk, 2-ahead 2sdclk"]
pub type INT_ST_AHEAD_MODE_W<'a, REG> = crate::FieldWriter<'a, REG, 2>;
impl R {
    #[doc = "Bits 0:1 - intoe on dat1 end ahead of time: 0/3-no, 1-ahead 1sdclk, 2-ahead 2sdclk"]
    #[inline(always)]
    pub fn intoe_end_ahead_mode(&self) -> INTOE_END_AHEAD_MODE_R {
        INTOE_END_AHEAD_MODE_R::new((self.bits & 3) as u8)
    }
    #[doc = "Bits 2:3 - int on dat1 end ahead of time: 0/3-no, 1-ahead 1sdclk, 2-ahead 2sdclk"]
    #[inline(always)]
    pub fn int_end_ahead_mode(&self) -> INT_END_AHEAD_MODE_R {
        INT_END_AHEAD_MODE_R::new(((self.bits >> 2) & 3) as u8)
    }
    #[doc = "Bits 4:5 - intoe on dat1 start ahead of time: 0/3-no, 1-ahead 1sdclk, 2-ahead 2sdclk"]
    #[inline(always)]
    pub fn intoe_st_ahead_mode(&self) -> INTOE_ST_AHEAD_MODE_R {
        INTOE_ST_AHEAD_MODE_R::new(((self.bits >> 4) & 3) as u8)
    }
    #[doc = "Bits 6:7 - int on dat1 start ahead of time: 0/3-no, 1-ahead 1sdclk, 2-ahead 2sdclk"]
    #[inline(always)]
    pub fn int_st_ahead_mode(&self) -> INT_ST_AHEAD_MODE_R {
        INT_ST_AHEAD_MODE_R::new(((self.bits >> 6) & 3) as u8)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("CFG_UHS1_INT_MODE")
            .field("intoe_end_ahead_mode", &self.intoe_end_ahead_mode())
            .field("int_end_ahead_mode", &self.int_end_ahead_mode())
            .field("intoe_st_ahead_mode", &self.intoe_st_ahead_mode())
            .field("int_st_ahead_mode", &self.int_st_ahead_mode())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:1 - intoe on dat1 end ahead of time: 0/3-no, 1-ahead 1sdclk, 2-ahead 2sdclk"]
    #[inline(always)]
    pub fn intoe_end_ahead_mode(&mut self) -> INTOE_END_AHEAD_MODE_W<'_, CFG_UHS1_INT_MODE_SPEC> {
        INTOE_END_AHEAD_MODE_W::new(self, 0)
    }
    #[doc = "Bits 2:3 - int on dat1 end ahead of time: 0/3-no, 1-ahead 1sdclk, 2-ahead 2sdclk"]
    #[inline(always)]
    pub fn int_end_ahead_mode(&mut self) -> INT_END_AHEAD_MODE_W<'_, CFG_UHS1_INT_MODE_SPEC> {
        INT_END_AHEAD_MODE_W::new(self, 2)
    }
    #[doc = "Bits 4:5 - intoe on dat1 start ahead of time: 0/3-no, 1-ahead 1sdclk, 2-ahead 2sdclk"]
    #[inline(always)]
    pub fn intoe_st_ahead_mode(&mut self) -> INTOE_ST_AHEAD_MODE_W<'_, CFG_UHS1_INT_MODE_SPEC> {
        INTOE_ST_AHEAD_MODE_W::new(self, 4)
    }
    #[doc = "Bits 6:7 - int on dat1 start ahead of time: 0/3-no, 1-ahead 1sdclk, 2-ahead 2sdclk"]
    #[inline(always)]
    pub fn int_st_ahead_mode(&mut self) -> INT_ST_AHEAD_MODE_W<'_, CFG_UHS1_INT_MODE_SPEC> {
        INT_ST_AHEAD_MODE_W::new(self, 6)
    }
}
#[doc = "configure int to start and end ahead of time in uhs1 mode\n\nYou can [`read`](crate::Reg::read) this register and get [`cfg_uhs1_int_mode::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`cfg_uhs1_int_mode::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct CFG_UHS1_INT_MODE_SPEC;
impl crate::RegisterSpec for CFG_UHS1_INT_MODE_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`cfg_uhs1_int_mode::R`](R) reader structure"]
impl crate::Readable for CFG_UHS1_INT_MODE_SPEC {}
#[doc = "`write(|w| ..)` method takes [`cfg_uhs1_int_mode::W`](W) writer structure"]
impl crate::Writable for CFG_UHS1_INT_MODE_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets CFG_UHS1_INT_MODE to value 0"]
impl crate::Resettable for CFG_UHS1_INT_MODE_SPEC {}
