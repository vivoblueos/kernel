#[doc = "Register `SYSCLK_FREQ_QUERY_0` reader"]
pub type R = crate::R<SYSCLK_FREQ_QUERY_0_SPEC>;
#[doc = "Field `FOSC_FREQ` reader - This field indicates the frequency(MHz) of FOSC."]
pub type FOSC_FREQ_R = crate::FieldReader;
#[doc = "Field `PLL_FREQ` reader - This field indicates the frequency(MHz) of SPLL."]
pub type PLL_FREQ_R = crate::FieldReader<u16>;
impl R {
    #[doc = "Bits 0:7 - This field indicates the frequency(MHz) of FOSC."]
    #[inline(always)]
    pub fn fosc_freq(&self) -> FOSC_FREQ_R {
        FOSC_FREQ_R::new((self.bits & 0xff) as u8)
    }
    #[doc = "Bits 8:17 - This field indicates the frequency(MHz) of SPLL."]
    #[inline(always)]
    pub fn pll_freq(&self) -> PLL_FREQ_R {
        PLL_FREQ_R::new(((self.bits >> 8) & 0x03ff) as u16)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("SYSCLK_FREQ_QUERY_0")
            .field("fosc_freq", &self.fosc_freq())
            .field("pll_freq", &self.pll_freq())
            .finish()
    }
}
#[doc = "SYSCLK frequency query 0 register\n\nYou can [`read`](crate::Reg::read) this register and get [`sysclk_freq_query_0::R`](R). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct SYSCLK_FREQ_QUERY_0_SPEC;
impl crate::RegisterSpec for SYSCLK_FREQ_QUERY_0_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`sysclk_freq_query_0::R`](R) reader structure"]
impl crate::Readable for SYSCLK_FREQ_QUERY_0_SPEC {}
#[doc = "`reset()` method sets SYSCLK_FREQ_QUERY_0 to value 0x0001_e014"]
impl crate::Resettable for SYSCLK_FREQ_QUERY_0_SPEC {
    const RESET_VALUE: u32 = 0x0001_e014;
}
