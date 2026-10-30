#[doc = "Register `SRAM_CLK` reader"]
pub type R = crate::R<SRAM_CLK_SPEC>;
#[doc = "Field `SCLKCNT_L` reader - For SPI0 external RAM interface, it must be equal to spi_mem_clkcnt_N."]
pub type SCLKCNT_L_R = crate::FieldReader;
#[doc = "Field `SCLKCNT_H` reader - For SPI0 external RAM interface, it must be floor((spi_mem_clkcnt_N+1)/2-1)."]
pub type SCLKCNT_H_R = crate::FieldReader;
#[doc = "Field `SCLKCNT_N` reader - For SPI0 external RAM interface, it is the divider of spi_mem_clk. So spi_mem_clk frequency is system/(spi_mem_clkcnt_N+1)"]
pub type SCLKCNT_N_R = crate::FieldReader;
#[doc = "Field `SCLK_EQU_SYSCLK` reader - For SPI0 external RAM interface, 1: spi_mem_clk is eqaul to system 0: spi_mem_clk is divided from system clock."]
pub type SCLK_EQU_SYSCLK_R = crate::BitReader;
impl R {
    #[doc = "Bits 0:7 - For SPI0 external RAM interface, it must be equal to spi_mem_clkcnt_N."]
    #[inline(always)]
    pub fn sclkcnt_l(&self) -> SCLKCNT_L_R {
        SCLKCNT_L_R::new((self.bits & 0xff) as u8)
    }
    #[doc = "Bits 8:15 - For SPI0 external RAM interface, it must be floor((spi_mem_clkcnt_N+1)/2-1)."]
    #[inline(always)]
    pub fn sclkcnt_h(&self) -> SCLKCNT_H_R {
        SCLKCNT_H_R::new(((self.bits >> 8) & 0xff) as u8)
    }
    #[doc = "Bits 16:23 - For SPI0 external RAM interface, it is the divider of spi_mem_clk. So spi_mem_clk frequency is system/(spi_mem_clkcnt_N+1)"]
    #[inline(always)]
    pub fn sclkcnt_n(&self) -> SCLKCNT_N_R {
        SCLKCNT_N_R::new(((self.bits >> 16) & 0xff) as u8)
    }
    #[doc = "Bit 31 - For SPI0 external RAM interface, 1: spi_mem_clk is eqaul to system 0: spi_mem_clk is divided from system clock."]
    #[inline(always)]
    pub fn sclk_equ_sysclk(&self) -> SCLK_EQU_SYSCLK_R {
        SCLK_EQU_SYSCLK_R::new(((self.bits >> 31) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("SRAM_CLK")
            .field("sclkcnt_l", &self.sclkcnt_l())
            .field("sclkcnt_h", &self.sclkcnt_h())
            .field("sclkcnt_n", &self.sclkcnt_n())
            .field("sclk_equ_sysclk", &self.sclk_equ_sysclk())
            .finish()
    }
}
#[doc = "SPI0 external RAM clock control register\n\nYou can [`read`](crate::Reg::read) this register and get [`sram_clk::R`](R). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct SRAM_CLK_SPEC;
impl crate::RegisterSpec for SRAM_CLK_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`sram_clk::R`](R) reader structure"]
impl crate::Readable for SRAM_CLK_SPEC {}
#[doc = "`reset()` method sets SRAM_CLK to value 0x0003_0103"]
impl crate::Resettable for SRAM_CLK_SPEC {
    const RESET_VALUE: u32 = 0x0003_0103;
}
