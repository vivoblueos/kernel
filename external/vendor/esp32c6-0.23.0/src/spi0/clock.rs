#[doc = "Register `CLOCK` reader"]
pub type R = crate::R<CLOCK_SPEC>;
#[doc = "Register `CLOCK` writer"]
pub type W = crate::W<CLOCK_SPEC>;
#[doc = "Field `CLKCNT_L` reader - In the master mode it must be equal to spi_mem_clkcnt_N."]
pub type CLKCNT_L_R = crate::FieldReader;
#[doc = "Field `CLKCNT_L` writer - In the master mode it must be equal to spi_mem_clkcnt_N."]
pub type CLKCNT_L_W<'a, REG> = crate::FieldWriter<'a, REG, 8>;
#[doc = "Field `CLKCNT_H` reader - In the master mode it must be floor((spi_mem_clkcnt_N+1)/2-1)."]
pub type CLKCNT_H_R = crate::FieldReader;
#[doc = "Field `CLKCNT_H` writer - In the master mode it must be floor((spi_mem_clkcnt_N+1)/2-1)."]
pub type CLKCNT_H_W<'a, REG> = crate::FieldWriter<'a, REG, 8>;
#[doc = "Field `CLKCNT_N` reader - In the master mode it is the divider of spi_mem_clk. So spi_mem_clk frequency is system/(spi_mem_clkcnt_N+1)"]
pub type CLKCNT_N_R = crate::FieldReader;
#[doc = "Field `CLKCNT_N` writer - In the master mode it is the divider of spi_mem_clk. So spi_mem_clk frequency is system/(spi_mem_clkcnt_N+1)"]
pub type CLKCNT_N_W<'a, REG> = crate::FieldWriter<'a, REG, 8>;
#[doc = "Field `CLK_EQU_SYSCLK` reader - 1: 1-division mode, the frequency of SPI bus clock equals to that of MSPI module clock."]
pub type CLK_EQU_SYSCLK_R = crate::BitReader;
#[doc = "Field `CLK_EQU_SYSCLK` writer - 1: 1-division mode, the frequency of SPI bus clock equals to that of MSPI module clock."]
pub type CLK_EQU_SYSCLK_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bits 0:7 - In the master mode it must be equal to spi_mem_clkcnt_N."]
    #[inline(always)]
    pub fn clkcnt_l(&self) -> CLKCNT_L_R {
        CLKCNT_L_R::new((self.bits & 0xff) as u8)
    }
    #[doc = "Bits 8:15 - In the master mode it must be floor((spi_mem_clkcnt_N+1)/2-1)."]
    #[inline(always)]
    pub fn clkcnt_h(&self) -> CLKCNT_H_R {
        CLKCNT_H_R::new(((self.bits >> 8) & 0xff) as u8)
    }
    #[doc = "Bits 16:23 - In the master mode it is the divider of spi_mem_clk. So spi_mem_clk frequency is system/(spi_mem_clkcnt_N+1)"]
    #[inline(always)]
    pub fn clkcnt_n(&self) -> CLKCNT_N_R {
        CLKCNT_N_R::new(((self.bits >> 16) & 0xff) as u8)
    }
    #[doc = "Bit 31 - 1: 1-division mode, the frequency of SPI bus clock equals to that of MSPI module clock."]
    #[inline(always)]
    pub fn clk_equ_sysclk(&self) -> CLK_EQU_SYSCLK_R {
        CLK_EQU_SYSCLK_R::new(((self.bits >> 31) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("CLOCK")
            .field("clkcnt_l", &self.clkcnt_l())
            .field("clkcnt_h", &self.clkcnt_h())
            .field("clkcnt_n", &self.clkcnt_n())
            .field("clk_equ_sysclk", &self.clk_equ_sysclk())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:7 - In the master mode it must be equal to spi_mem_clkcnt_N."]
    #[inline(always)]
    pub fn clkcnt_l(&mut self) -> CLKCNT_L_W<'_, CLOCK_SPEC> {
        CLKCNT_L_W::new(self, 0)
    }
    #[doc = "Bits 8:15 - In the master mode it must be floor((spi_mem_clkcnt_N+1)/2-1)."]
    #[inline(always)]
    pub fn clkcnt_h(&mut self) -> CLKCNT_H_W<'_, CLOCK_SPEC> {
        CLKCNT_H_W::new(self, 8)
    }
    #[doc = "Bits 16:23 - In the master mode it is the divider of spi_mem_clk. So spi_mem_clk frequency is system/(spi_mem_clkcnt_N+1)"]
    #[inline(always)]
    pub fn clkcnt_n(&mut self) -> CLKCNT_N_W<'_, CLOCK_SPEC> {
        CLKCNT_N_W::new(self, 16)
    }
    #[doc = "Bit 31 - 1: 1-division mode, the frequency of SPI bus clock equals to that of MSPI module clock."]
    #[inline(always)]
    pub fn clk_equ_sysclk(&mut self) -> CLK_EQU_SYSCLK_W<'_, CLOCK_SPEC> {
        CLK_EQU_SYSCLK_W::new(self, 31)
    }
}
#[doc = "SPI clock division control register.\n\nYou can [`read`](crate::Reg::read) this register and get [`clock::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`clock::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct CLOCK_SPEC;
impl crate::RegisterSpec for CLOCK_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`clock::R`](R) reader structure"]
impl crate::Readable for CLOCK_SPEC {}
#[doc = "`write(|w| ..)` method takes [`clock::W`](W) writer structure"]
impl crate::Writable for CLOCK_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets CLOCK to value 0x0003_0103"]
impl crate::Resettable for CLOCK_SPEC {
    const RESET_VALUE: u32 = 0x0003_0103;
}
