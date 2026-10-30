#[doc = "Register `TOKEN_CON` writer"]
pub type W = crate::W<TOKEN_CON_SPEC>;
#[doc = "Field `SLC0HOST_TOKEN0_DEC` writer - *******Description***********"]
pub type SLC0HOST_TOKEN0_DEC_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SLC0HOST_TOKEN1_DEC` writer - *******Description***********"]
pub type SLC0HOST_TOKEN1_DEC_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SLC0HOST_TOKEN0_WR` writer - *******Description***********"]
pub type SLC0HOST_TOKEN0_WR_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SLC0HOST_TOKEN1_WR` writer - *******Description***********"]
pub type SLC0HOST_TOKEN1_WR_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SLC1HOST_TOKEN0_DEC` writer - *******Description***********"]
pub type SLC1HOST_TOKEN0_DEC_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SLC1HOST_TOKEN1_DEC` writer - *******Description***********"]
pub type SLC1HOST_TOKEN1_DEC_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SLC1HOST_TOKEN0_WR` writer - *******Description***********"]
pub type SLC1HOST_TOKEN0_WR_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SLC1HOST_TOKEN1_WR` writer - *******Description***********"]
pub type SLC1HOST_TOKEN1_WR_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SLC0HOST_LEN_WR` writer - *******Description***********"]
pub type SLC0HOST_LEN_WR_W<'a, REG> = crate::BitWriter<'a, REG>;
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for crate::generic::Reg<TOKEN_CON_SPEC> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "(not readable)")
    }
}
impl W {
    #[doc = "Bit 0 - *******Description***********"]
    #[inline(always)]
    pub fn slc0host_token0_dec(&mut self) -> SLC0HOST_TOKEN0_DEC_W<'_, TOKEN_CON_SPEC> {
        SLC0HOST_TOKEN0_DEC_W::new(self, 0)
    }
    #[doc = "Bit 1 - *******Description***********"]
    #[inline(always)]
    pub fn slc0host_token1_dec(&mut self) -> SLC0HOST_TOKEN1_DEC_W<'_, TOKEN_CON_SPEC> {
        SLC0HOST_TOKEN1_DEC_W::new(self, 1)
    }
    #[doc = "Bit 2 - *******Description***********"]
    #[inline(always)]
    pub fn slc0host_token0_wr(&mut self) -> SLC0HOST_TOKEN0_WR_W<'_, TOKEN_CON_SPEC> {
        SLC0HOST_TOKEN0_WR_W::new(self, 2)
    }
    #[doc = "Bit 3 - *******Description***********"]
    #[inline(always)]
    pub fn slc0host_token1_wr(&mut self) -> SLC0HOST_TOKEN1_WR_W<'_, TOKEN_CON_SPEC> {
        SLC0HOST_TOKEN1_WR_W::new(self, 3)
    }
    #[doc = "Bit 4 - *******Description***********"]
    #[inline(always)]
    pub fn slc1host_token0_dec(&mut self) -> SLC1HOST_TOKEN0_DEC_W<'_, TOKEN_CON_SPEC> {
        SLC1HOST_TOKEN0_DEC_W::new(self, 4)
    }
    #[doc = "Bit 5 - *******Description***********"]
    #[inline(always)]
    pub fn slc1host_token1_dec(&mut self) -> SLC1HOST_TOKEN1_DEC_W<'_, TOKEN_CON_SPEC> {
        SLC1HOST_TOKEN1_DEC_W::new(self, 5)
    }
    #[doc = "Bit 6 - *******Description***********"]
    #[inline(always)]
    pub fn slc1host_token0_wr(&mut self) -> SLC1HOST_TOKEN0_WR_W<'_, TOKEN_CON_SPEC> {
        SLC1HOST_TOKEN0_WR_W::new(self, 6)
    }
    #[doc = "Bit 7 - *******Description***********"]
    #[inline(always)]
    pub fn slc1host_token1_wr(&mut self) -> SLC1HOST_TOKEN1_WR_W<'_, TOKEN_CON_SPEC> {
        SLC1HOST_TOKEN1_WR_W::new(self, 7)
    }
    #[doc = "Bit 8 - *******Description***********"]
    #[inline(always)]
    pub fn slc0host_len_wr(&mut self) -> SLC0HOST_LEN_WR_W<'_, TOKEN_CON_SPEC> {
        SLC0HOST_LEN_WR_W::new(self, 8)
    }
}
#[doc = "*******Description***********\n\nYou can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`token_con::W`](W). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct TOKEN_CON_SPEC;
impl crate::RegisterSpec for TOKEN_CON_SPEC {
    type Ux = u32;
}
#[doc = "`write(|w| ..)` method takes [`token_con::W`](W) writer structure"]
impl crate::Writable for TOKEN_CON_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets TOKEN_CON to value 0"]
impl crate::Resettable for TOKEN_CON_SPEC {}
