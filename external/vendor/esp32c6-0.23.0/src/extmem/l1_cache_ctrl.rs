#[doc = "Register `L1_CACHE_CTRL` reader"]
pub type R = crate::R<L1_CACHE_CTRL_SPEC>;
#[doc = "Register `L1_CACHE_CTRL` writer"]
pub type W = crate::W<L1_CACHE_CTRL_SPEC>;
#[doc = "Field `L1_CACHE_SHUT_BUS0` reader - The bit is used to disable core0 dbus access L1-Cache, 0: enable, 1: disable"]
pub type L1_CACHE_SHUT_BUS0_R = crate::BitReader;
#[doc = "Field `L1_CACHE_SHUT_BUS0` writer - The bit is used to disable core0 dbus access L1-Cache, 0: enable, 1: disable"]
pub type L1_CACHE_SHUT_BUS0_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `L1_CACHE_SHUT_BUS1` reader - The bit is used to disable core1 dbus access L1-Cache, 0: enable, 1: disable"]
pub type L1_CACHE_SHUT_BUS1_R = crate::BitReader;
#[doc = "Field `L1_CACHE_SHUT_BUS1` writer - The bit is used to disable core1 dbus access L1-Cache, 0: enable, 1: disable"]
pub type L1_CACHE_SHUT_BUS1_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `L1_CACHE_SHUT_DBUS2` reader - Reserved"]
pub type L1_CACHE_SHUT_DBUS2_R = crate::BitReader;
#[doc = "Field `L1_CACHE_SHUT_DBUS3` reader - Reserved"]
pub type L1_CACHE_SHUT_DBUS3_R = crate::BitReader;
#[doc = "Field `L1_CACHE_SHUT_DMA` reader - The bit is used to disable DMA access L1-Cache, 0: enable, 1: disable"]
pub type L1_CACHE_SHUT_DMA_R = crate::BitReader;
#[doc = "Field `L1_CACHE_UNDEF_OP` reader - Reserved"]
pub type L1_CACHE_UNDEF_OP_R = crate::FieldReader;
#[doc = "Field `L1_CACHE_UNDEF_OP` writer - Reserved"]
pub type L1_CACHE_UNDEF_OP_W<'a, REG> = crate::FieldWriter<'a, REG, 4>;
impl R {
    #[doc = "Bit 0 - The bit is used to disable core0 dbus access L1-Cache, 0: enable, 1: disable"]
    #[inline(always)]
    pub fn l1_cache_shut_bus0(&self) -> L1_CACHE_SHUT_BUS0_R {
        L1_CACHE_SHUT_BUS0_R::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - The bit is used to disable core1 dbus access L1-Cache, 0: enable, 1: disable"]
    #[inline(always)]
    pub fn l1_cache_shut_bus1(&self) -> L1_CACHE_SHUT_BUS1_R {
        L1_CACHE_SHUT_BUS1_R::new(((self.bits >> 1) & 1) != 0)
    }
    #[doc = "Bit 2 - Reserved"]
    #[inline(always)]
    pub fn l1_cache_shut_dbus2(&self) -> L1_CACHE_SHUT_DBUS2_R {
        L1_CACHE_SHUT_DBUS2_R::new(((self.bits >> 2) & 1) != 0)
    }
    #[doc = "Bit 3 - Reserved"]
    #[inline(always)]
    pub fn l1_cache_shut_dbus3(&self) -> L1_CACHE_SHUT_DBUS3_R {
        L1_CACHE_SHUT_DBUS3_R::new(((self.bits >> 3) & 1) != 0)
    }
    #[doc = "Bit 4 - The bit is used to disable DMA access L1-Cache, 0: enable, 1: disable"]
    #[inline(always)]
    pub fn l1_cache_shut_dma(&self) -> L1_CACHE_SHUT_DMA_R {
        L1_CACHE_SHUT_DMA_R::new(((self.bits >> 4) & 1) != 0)
    }
    #[doc = "Bits 8:11 - Reserved"]
    #[inline(always)]
    pub fn l1_cache_undef_op(&self) -> L1_CACHE_UNDEF_OP_R {
        L1_CACHE_UNDEF_OP_R::new(((self.bits >> 8) & 0x0f) as u8)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("L1_CACHE_CTRL")
            .field("l1_cache_shut_bus0", &self.l1_cache_shut_bus0())
            .field("l1_cache_shut_bus1", &self.l1_cache_shut_bus1())
            .field("l1_cache_shut_dbus2", &self.l1_cache_shut_dbus2())
            .field("l1_cache_shut_dbus3", &self.l1_cache_shut_dbus3())
            .field("l1_cache_shut_dma", &self.l1_cache_shut_dma())
            .field("l1_cache_undef_op", &self.l1_cache_undef_op())
            .finish()
    }
}
impl W {
    #[doc = "Bit 0 - The bit is used to disable core0 dbus access L1-Cache, 0: enable, 1: disable"]
    #[inline(always)]
    pub fn l1_cache_shut_bus0(&mut self) -> L1_CACHE_SHUT_BUS0_W<'_, L1_CACHE_CTRL_SPEC> {
        L1_CACHE_SHUT_BUS0_W::new(self, 0)
    }
    #[doc = "Bit 1 - The bit is used to disable core1 dbus access L1-Cache, 0: enable, 1: disable"]
    #[inline(always)]
    pub fn l1_cache_shut_bus1(&mut self) -> L1_CACHE_SHUT_BUS1_W<'_, L1_CACHE_CTRL_SPEC> {
        L1_CACHE_SHUT_BUS1_W::new(self, 1)
    }
    #[doc = "Bits 8:11 - Reserved"]
    #[inline(always)]
    pub fn l1_cache_undef_op(&mut self) -> L1_CACHE_UNDEF_OP_W<'_, L1_CACHE_CTRL_SPEC> {
        L1_CACHE_UNDEF_OP_W::new(self, 8)
    }
}
#[doc = "L1 data Cache(L1-Cache) control register\n\nYou can [`read`](crate::Reg::read) this register and get [`l1_cache_ctrl::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`l1_cache_ctrl::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct L1_CACHE_CTRL_SPEC;
impl crate::RegisterSpec for L1_CACHE_CTRL_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`l1_cache_ctrl::R`](R) reader structure"]
impl crate::Readable for L1_CACHE_CTRL_SPEC {}
#[doc = "`write(|w| ..)` method takes [`l1_cache_ctrl::W`](W) writer structure"]
impl crate::Writable for L1_CACHE_CTRL_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets L1_CACHE_CTRL to value 0"]
impl crate::Resettable for L1_CACHE_CTRL_SPEC {}
