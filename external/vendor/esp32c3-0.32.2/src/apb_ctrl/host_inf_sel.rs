#[doc = "Register `HOST_INF_SEL` reader"]
pub type R = crate::R<HOST_INF_SEL_SPEC>;
#[doc = "Register `HOST_INF_SEL` writer"]
pub type W = crate::W<HOST_INF_SEL_SPEC>;
#[doc = "Field `PERI_IO_SWAP` reader - reg_peri_io_swap"]
pub type PERI_IO_SWAP_R = crate::FieldReader;
#[doc = "Field `PERI_IO_SWAP` writer - reg_peri_io_swap"]
pub type PERI_IO_SWAP_W<'a, REG> = crate::FieldWriter<'a, REG, 8>;
impl R {
    #[doc = "Bits 0:7 - reg_peri_io_swap"]
    #[inline(always)]
    pub fn peri_io_swap(&self) -> PERI_IO_SWAP_R {
        PERI_IO_SWAP_R::new((self.bits & 0xff) as u8)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("HOST_INF_SEL")
            .field("peri_io_swap", &self.peri_io_swap())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:7 - reg_peri_io_swap"]
    #[inline(always)]
    pub fn peri_io_swap(&mut self) -> PERI_IO_SWAP_W<'_, HOST_INF_SEL_SPEC> {
        PERI_IO_SWAP_W::new(self, 0)
    }
}
#[doc = "APB_CTRL_HOST_INF_SEL_REG\n\nYou can [`read`](crate::Reg::read) this register and get [`host_inf_sel::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`host_inf_sel::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct HOST_INF_SEL_SPEC;
impl crate::RegisterSpec for HOST_INF_SEL_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`host_inf_sel::R`](R) reader structure"]
impl crate::Readable for HOST_INF_SEL_SPEC {}
#[doc = "`write(|w| ..)` method takes [`host_inf_sel::W`](W) writer structure"]
impl crate::Writable for HOST_INF_SEL_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets HOST_INF_SEL to value 0"]
impl crate::Resettable for HOST_INF_SEL_SPEC {}
