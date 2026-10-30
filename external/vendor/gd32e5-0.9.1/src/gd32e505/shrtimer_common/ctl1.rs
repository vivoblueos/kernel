#[doc = "Register `CTL1` reader"]
pub type R = crate::R<Ctl1Spec>;
#[doc = "Register `CTL1` writer"]
pub type W = crate::W<Ctl1Spec>;
#[doc = "Field `MTSUP` reader - Master_TIMER software update"]
pub type MtsupR = crate::BitReader;
#[doc = "Field `MTSUP` writer - Master_TIMER software update"]
pub type MtsupW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ST0SUP` reader - Slave_TIMER0 software update"]
pub type St0supR = crate::BitReader;
#[doc = "Field `ST0SUP` writer - Slave_TIMER0 software update"]
pub type St0supW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ST1SUP` reader - Slave_TIMER1 software update"]
pub type St1supR = crate::BitReader;
#[doc = "Field `ST1SUP` writer - Slave_TIMER1 software update"]
pub type St1supW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ST2SUP` reader - Slave_TIMER2 software update"]
pub type St2supR = crate::BitReader;
#[doc = "Field `ST2SUP` writer - Slave_TIMER2 software update"]
pub type St2supW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ST3SUP` reader - Slave_TIMER3 software update"]
pub type St3supR = crate::BitReader;
#[doc = "Field `ST3SUP` writer - Slave_TIMER3 software update"]
pub type St3supW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ST4SUP` reader - Slave_TIMER4 software update"]
pub type St4supR = crate::BitReader;
#[doc = "Field `ST4SUP` writer - Slave_TIMER4 software update"]
pub type St4supW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `MTSRST` reader - Master_TIMER software reset"]
pub type MtsrstR = crate::BitReader;
#[doc = "Field `MTSRST` writer - Master_TIMER software reset"]
pub type MtsrstW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ST0SRST` reader - Slave_TIMER0 software reset"]
pub type St0srstR = crate::BitReader;
#[doc = "Field `ST0SRST` writer - Slave_TIMER0 software reset"]
pub type St0srstW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ST1SRST` reader - Slave_TIMER1 software reset"]
pub type St1srstR = crate::BitReader;
#[doc = "Field `ST1SRST` writer - Slave_TIMER1 software reset"]
pub type St1srstW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ST2SRST` reader - Slave_TIMER2 software reset"]
pub type St2srstR = crate::BitReader;
#[doc = "Field `ST2SRST` writer - Slave_TIMER2 software reset"]
pub type St2srstW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ST3SRST` reader - Slave_TIMER3 software reset"]
pub type St3srstR = crate::BitReader;
#[doc = "Field `ST3SRST` writer - Slave_TIMER3 software reset"]
pub type St3srstW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ST4SRST` reader - Slave_TIMER4 software reset"]
pub type St4srstR = crate::BitReader;
#[doc = "Field `ST4SRST` writer - Slave_TIMER4 software reset"]
pub type St4srstW<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 0 - Master_TIMER software update"]
    #[inline(always)]
    pub fn mtsup(&self) -> MtsupR {
        MtsupR::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - Slave_TIMER0 software update"]
    #[inline(always)]
    pub fn st0sup(&self) -> St0supR {
        St0supR::new(((self.bits >> 1) & 1) != 0)
    }
    #[doc = "Bit 2 - Slave_TIMER1 software update"]
    #[inline(always)]
    pub fn st1sup(&self) -> St1supR {
        St1supR::new(((self.bits >> 2) & 1) != 0)
    }
    #[doc = "Bit 3 - Slave_TIMER2 software update"]
    #[inline(always)]
    pub fn st2sup(&self) -> St2supR {
        St2supR::new(((self.bits >> 3) & 1) != 0)
    }
    #[doc = "Bit 4 - Slave_TIMER3 software update"]
    #[inline(always)]
    pub fn st3sup(&self) -> St3supR {
        St3supR::new(((self.bits >> 4) & 1) != 0)
    }
    #[doc = "Bit 5 - Slave_TIMER4 software update"]
    #[inline(always)]
    pub fn st4sup(&self) -> St4supR {
        St4supR::new(((self.bits >> 5) & 1) != 0)
    }
    #[doc = "Bit 8 - Master_TIMER software reset"]
    #[inline(always)]
    pub fn mtsrst(&self) -> MtsrstR {
        MtsrstR::new(((self.bits >> 8) & 1) != 0)
    }
    #[doc = "Bit 9 - Slave_TIMER0 software reset"]
    #[inline(always)]
    pub fn st0srst(&self) -> St0srstR {
        St0srstR::new(((self.bits >> 9) & 1) != 0)
    }
    #[doc = "Bit 10 - Slave_TIMER1 software reset"]
    #[inline(always)]
    pub fn st1srst(&self) -> St1srstR {
        St1srstR::new(((self.bits >> 10) & 1) != 0)
    }
    #[doc = "Bit 11 - Slave_TIMER2 software reset"]
    #[inline(always)]
    pub fn st2srst(&self) -> St2srstR {
        St2srstR::new(((self.bits >> 11) & 1) != 0)
    }
    #[doc = "Bit 12 - Slave_TIMER3 software reset"]
    #[inline(always)]
    pub fn st3srst(&self) -> St3srstR {
        St3srstR::new(((self.bits >> 12) & 1) != 0)
    }
    #[doc = "Bit 13 - Slave_TIMER4 software reset"]
    #[inline(always)]
    pub fn st4srst(&self) -> St4srstR {
        St4srstR::new(((self.bits >> 13) & 1) != 0)
    }
}
impl W {
    #[doc = "Bit 0 - Master_TIMER software update"]
    #[inline(always)]
    #[must_use]
    pub fn mtsup(&mut self) -> MtsupW<Ctl1Spec> {
        MtsupW::new(self, 0)
    }
    #[doc = "Bit 1 - Slave_TIMER0 software update"]
    #[inline(always)]
    #[must_use]
    pub fn st0sup(&mut self) -> St0supW<Ctl1Spec> {
        St0supW::new(self, 1)
    }
    #[doc = "Bit 2 - Slave_TIMER1 software update"]
    #[inline(always)]
    #[must_use]
    pub fn st1sup(&mut self) -> St1supW<Ctl1Spec> {
        St1supW::new(self, 2)
    }
    #[doc = "Bit 3 - Slave_TIMER2 software update"]
    #[inline(always)]
    #[must_use]
    pub fn st2sup(&mut self) -> St2supW<Ctl1Spec> {
        St2supW::new(self, 3)
    }
    #[doc = "Bit 4 - Slave_TIMER3 software update"]
    #[inline(always)]
    #[must_use]
    pub fn st3sup(&mut self) -> St3supW<Ctl1Spec> {
        St3supW::new(self, 4)
    }
    #[doc = "Bit 5 - Slave_TIMER4 software update"]
    #[inline(always)]
    #[must_use]
    pub fn st4sup(&mut self) -> St4supW<Ctl1Spec> {
        St4supW::new(self, 5)
    }
    #[doc = "Bit 8 - Master_TIMER software reset"]
    #[inline(always)]
    #[must_use]
    pub fn mtsrst(&mut self) -> MtsrstW<Ctl1Spec> {
        MtsrstW::new(self, 8)
    }
    #[doc = "Bit 9 - Slave_TIMER0 software reset"]
    #[inline(always)]
    #[must_use]
    pub fn st0srst(&mut self) -> St0srstW<Ctl1Spec> {
        St0srstW::new(self, 9)
    }
    #[doc = "Bit 10 - Slave_TIMER1 software reset"]
    #[inline(always)]
    #[must_use]
    pub fn st1srst(&mut self) -> St1srstW<Ctl1Spec> {
        St1srstW::new(self, 10)
    }
    #[doc = "Bit 11 - Slave_TIMER2 software reset"]
    #[inline(always)]
    #[must_use]
    pub fn st2srst(&mut self) -> St2srstW<Ctl1Spec> {
        St2srstW::new(self, 11)
    }
    #[doc = "Bit 12 - Slave_TIMER3 software reset"]
    #[inline(always)]
    #[must_use]
    pub fn st3srst(&mut self) -> St3srstW<Ctl1Spec> {
        St3srstW::new(self, 12)
    }
    #[doc = "Bit 13 - Slave_TIMER4 software reset"]
    #[inline(always)]
    #[must_use]
    pub fn st4srst(&mut self) -> St4srstW<Ctl1Spec> {
        St4srstW::new(self, 13)
    }
}
#[doc = "SHRTIMER control register 1\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`ctl1::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`ctl1::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct Ctl1Spec;
impl crate::RegisterSpec for Ctl1Spec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`ctl1::R`](R) reader structure"]
impl crate::Readable for Ctl1Spec {}
#[doc = "`write(|w| ..)` method takes [`ctl1::W`](W) writer structure"]
impl crate::Writable for Ctl1Spec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets CTL1 to value 0"]
impl crate::Resettable for Ctl1Spec {
    const RESET_VALUE: u32 = 0;
}
