#[doc = "Register `QCTL` reader"]
pub type R = crate::R<QctlSpec>;
#[doc = "Register `QCTL` writer"]
pub type W = crate::W<QctlSpec>;
#[doc = "Field `QMOD` reader - Quad-SPI mode enable"]
pub type QmodR = crate::BitReader;
#[doc = "Field `QMOD` writer - Quad-SPI mode enable"]
pub type QmodW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `QRD` reader - Quad-SPI mode read select"]
pub type QrdR = crate::BitReader;
#[doc = "Field `QRD` writer - Quad-SPI mode read select"]
pub type QrdW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `IO23_DRV` reader - Drive IO2 and IO3 enable"]
pub type Io23DrvR = crate::BitReader;
#[doc = "Field `IO23_DRV` writer - Drive IO2 and IO3 enable"]
pub type Io23DrvW<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 0 - Quad-SPI mode enable"]
    #[inline(always)]
    pub fn qmod(&self) -> QmodR {
        QmodR::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - Quad-SPI mode read select"]
    #[inline(always)]
    pub fn qrd(&self) -> QrdR {
        QrdR::new(((self.bits >> 1) & 1) != 0)
    }
    #[doc = "Bit 2 - Drive IO2 and IO3 enable"]
    #[inline(always)]
    pub fn io23_drv(&self) -> Io23DrvR {
        Io23DrvR::new(((self.bits >> 2) & 1) != 0)
    }
}
impl W {
    #[doc = "Bit 0 - Quad-SPI mode enable"]
    #[inline(always)]
    #[must_use]
    pub fn qmod(&mut self) -> QmodW<QctlSpec> {
        QmodW::new(self, 0)
    }
    #[doc = "Bit 1 - Quad-SPI mode read select"]
    #[inline(always)]
    #[must_use]
    pub fn qrd(&mut self) -> QrdW<QctlSpec> {
        QrdW::new(self, 1)
    }
    #[doc = "Bit 2 - Drive IO2 and IO3 enable"]
    #[inline(always)]
    #[must_use]
    pub fn io23_drv(&mut self) -> Io23DrvW<QctlSpec> {
        Io23DrvW::new(self, 2)
    }
}
#[doc = "Quad-SPI mode control register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`qctl::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`qctl::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct QctlSpec;
impl crate::RegisterSpec for QctlSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`qctl::R`](R) reader structure"]
impl crate::Readable for QctlSpec {}
#[doc = "`write(|w| ..)` method takes [`qctl::W`](W) writer structure"]
impl crate::Writable for QctlSpec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets QCTL to value 0"]
impl crate::Resettable for QctlSpec {
    const RESET_VALUE: u32 = 0;
}
