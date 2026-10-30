#[doc = "Register `SLC_APBWIN_CONF` reader"]
pub type R = crate::R<SLC_APBWIN_CONF_SPEC>;
#[doc = "Register `SLC_APBWIN_CONF` writer"]
pub type W = crate::W<SLC_APBWIN_CONF_SPEC>;
#[doc = "Field `SLC_APBWIN_ADDR` reader - *******Description***********"]
pub type SLC_APBWIN_ADDR_R = crate::FieldReader<u32>;
#[doc = "Field `SLC_APBWIN_ADDR` writer - *******Description***********"]
pub type SLC_APBWIN_ADDR_W<'a, REG> = crate::FieldWriter<'a, REG, 28, u32>;
#[doc = "Field `SLC_APBWIN_WR` reader - *******Description***********"]
pub type SLC_APBWIN_WR_R = crate::BitReader;
#[doc = "Field `SLC_APBWIN_WR` writer - *******Description***********"]
pub type SLC_APBWIN_WR_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SLC_APBWIN_START` reader - *******Description***********"]
pub type SLC_APBWIN_START_R = crate::BitReader;
#[doc = "Field `SLC_APBWIN_START` writer - *******Description***********"]
pub type SLC_APBWIN_START_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bits 0:27 - *******Description***********"]
    #[inline(always)]
    pub fn slc_apbwin_addr(&self) -> SLC_APBWIN_ADDR_R {
        SLC_APBWIN_ADDR_R::new(self.bits & 0x0fff_ffff)
    }
    #[doc = "Bit 28 - *******Description***********"]
    #[inline(always)]
    pub fn slc_apbwin_wr(&self) -> SLC_APBWIN_WR_R {
        SLC_APBWIN_WR_R::new(((self.bits >> 28) & 1) != 0)
    }
    #[doc = "Bit 29 - *******Description***********"]
    #[inline(always)]
    pub fn slc_apbwin_start(&self) -> SLC_APBWIN_START_R {
        SLC_APBWIN_START_R::new(((self.bits >> 29) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("SLC_APBWIN_CONF")
            .field("slc_apbwin_addr", &self.slc_apbwin_addr())
            .field("slc_apbwin_wr", &self.slc_apbwin_wr())
            .field("slc_apbwin_start", &self.slc_apbwin_start())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:27 - *******Description***********"]
    #[inline(always)]
    pub fn slc_apbwin_addr(&mut self) -> SLC_APBWIN_ADDR_W<'_, SLC_APBWIN_CONF_SPEC> {
        SLC_APBWIN_ADDR_W::new(self, 0)
    }
    #[doc = "Bit 28 - *******Description***********"]
    #[inline(always)]
    pub fn slc_apbwin_wr(&mut self) -> SLC_APBWIN_WR_W<'_, SLC_APBWIN_CONF_SPEC> {
        SLC_APBWIN_WR_W::new(self, 28)
    }
    #[doc = "Bit 29 - *******Description***********"]
    #[inline(always)]
    pub fn slc_apbwin_start(&mut self) -> SLC_APBWIN_START_W<'_, SLC_APBWIN_CONF_SPEC> {
        SLC_APBWIN_START_W::new(self, 29)
    }
}
#[doc = "*******Description***********\n\nYou can [`read`](crate::Reg::read) this register and get [`slc_apbwin_conf::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`slc_apbwin_conf::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct SLC_APBWIN_CONF_SPEC;
impl crate::RegisterSpec for SLC_APBWIN_CONF_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`slc_apbwin_conf::R`](R) reader structure"]
impl crate::Readable for SLC_APBWIN_CONF_SPEC {}
#[doc = "`write(|w| ..)` method takes [`slc_apbwin_conf::W`](W) writer structure"]
impl crate::Writable for SLC_APBWIN_CONF_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets SLC_APBWIN_CONF to value 0"]
impl crate::Resettable for SLC_APBWIN_CONF_SPEC {}
