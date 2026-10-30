#[doc = "Register `JFIFO_ST` reader"]
pub type R = crate::R<JFIFO_ST_SPEC>;
#[doc = "Register `JFIFO_ST` writer"]
pub type W = crate::W<JFIFO_ST_SPEC>;
#[doc = "Field `IN_FIFO_CNT` reader - JTAT in fifo counter."]
pub type IN_FIFO_CNT_R = crate::FieldReader;
#[doc = "Field `IN_FIFO_EMPTY` reader - 1: JTAG in fifo is empty."]
pub type IN_FIFO_EMPTY_R = crate::BitReader;
#[doc = "Field `IN_FIFO_FULL` reader - 1: JTAG in fifo is full."]
pub type IN_FIFO_FULL_R = crate::BitReader;
#[doc = "Field `OUT_FIFO_CNT` reader - JTAT out fifo counter."]
pub type OUT_FIFO_CNT_R = crate::FieldReader;
#[doc = "Field `OUT_FIFO_EMPTY` reader - 1: JTAG out fifo is empty."]
pub type OUT_FIFO_EMPTY_R = crate::BitReader;
#[doc = "Field `OUT_FIFO_FULL` reader - 1: JTAG out fifo is full."]
pub type OUT_FIFO_FULL_R = crate::BitReader;
#[doc = "Field `IN_FIFO_RESET` reader - Write 1 to reset JTAG in fifo."]
pub type IN_FIFO_RESET_R = crate::BitReader;
#[doc = "Field `IN_FIFO_RESET` writer - Write 1 to reset JTAG in fifo."]
pub type IN_FIFO_RESET_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `OUT_FIFO_RESET` reader - Write 1 to reset JTAG out fifo."]
pub type OUT_FIFO_RESET_R = crate::BitReader;
#[doc = "Field `OUT_FIFO_RESET` writer - Write 1 to reset JTAG out fifo."]
pub type OUT_FIFO_RESET_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bits 0:1 - JTAT in fifo counter."]
    #[inline(always)]
    pub fn in_fifo_cnt(&self) -> IN_FIFO_CNT_R {
        IN_FIFO_CNT_R::new((self.bits & 3) as u8)
    }
    #[doc = "Bit 2 - 1: JTAG in fifo is empty."]
    #[inline(always)]
    pub fn in_fifo_empty(&self) -> IN_FIFO_EMPTY_R {
        IN_FIFO_EMPTY_R::new(((self.bits >> 2) & 1) != 0)
    }
    #[doc = "Bit 3 - 1: JTAG in fifo is full."]
    #[inline(always)]
    pub fn in_fifo_full(&self) -> IN_FIFO_FULL_R {
        IN_FIFO_FULL_R::new(((self.bits >> 3) & 1) != 0)
    }
    #[doc = "Bits 4:5 - JTAT out fifo counter."]
    #[inline(always)]
    pub fn out_fifo_cnt(&self) -> OUT_FIFO_CNT_R {
        OUT_FIFO_CNT_R::new(((self.bits >> 4) & 3) as u8)
    }
    #[doc = "Bit 6 - 1: JTAG out fifo is empty."]
    #[inline(always)]
    pub fn out_fifo_empty(&self) -> OUT_FIFO_EMPTY_R {
        OUT_FIFO_EMPTY_R::new(((self.bits >> 6) & 1) != 0)
    }
    #[doc = "Bit 7 - 1: JTAG out fifo is full."]
    #[inline(always)]
    pub fn out_fifo_full(&self) -> OUT_FIFO_FULL_R {
        OUT_FIFO_FULL_R::new(((self.bits >> 7) & 1) != 0)
    }
    #[doc = "Bit 8 - Write 1 to reset JTAG in fifo."]
    #[inline(always)]
    pub fn in_fifo_reset(&self) -> IN_FIFO_RESET_R {
        IN_FIFO_RESET_R::new(((self.bits >> 8) & 1) != 0)
    }
    #[doc = "Bit 9 - Write 1 to reset JTAG out fifo."]
    #[inline(always)]
    pub fn out_fifo_reset(&self) -> OUT_FIFO_RESET_R {
        OUT_FIFO_RESET_R::new(((self.bits >> 9) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("JFIFO_ST")
            .field("in_fifo_cnt", &self.in_fifo_cnt())
            .field("in_fifo_empty", &self.in_fifo_empty())
            .field("in_fifo_full", &self.in_fifo_full())
            .field("out_fifo_cnt", &self.out_fifo_cnt())
            .field("out_fifo_empty", &self.out_fifo_empty())
            .field("out_fifo_full", &self.out_fifo_full())
            .field("in_fifo_reset", &self.in_fifo_reset())
            .field("out_fifo_reset", &self.out_fifo_reset())
            .finish()
    }
}
impl W {
    #[doc = "Bit 8 - Write 1 to reset JTAG in fifo."]
    #[inline(always)]
    pub fn in_fifo_reset(&mut self) -> IN_FIFO_RESET_W<'_, JFIFO_ST_SPEC> {
        IN_FIFO_RESET_W::new(self, 8)
    }
    #[doc = "Bit 9 - Write 1 to reset JTAG out fifo."]
    #[inline(always)]
    pub fn out_fifo_reset(&mut self) -> OUT_FIFO_RESET_W<'_, JFIFO_ST_SPEC> {
        OUT_FIFO_RESET_W::new(self, 9)
    }
}
#[doc = "USB_DEVICE_JFIFO_ST_REG.\n\nYou can [`read`](crate::Reg::read) this register and get [`jfifo_st::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`jfifo_st::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct JFIFO_ST_SPEC;
impl crate::RegisterSpec for JFIFO_ST_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`jfifo_st::R`](R) reader structure"]
impl crate::Readable for JFIFO_ST_SPEC {}
#[doc = "`write(|w| ..)` method takes [`jfifo_st::W`](W) writer structure"]
impl crate::Writable for JFIFO_ST_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets JFIFO_ST to value 0x44"]
impl crate::Resettable for JFIFO_ST_SPEC {
    const RESET_VALUE: u32 = 0x44;
}
