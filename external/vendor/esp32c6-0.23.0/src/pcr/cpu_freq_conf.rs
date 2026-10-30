#[doc = "Register `CPU_FREQ_CONF` reader"]
pub type R = crate::R<CPU_FREQ_CONF_SPEC>;
#[doc = "Register `CPU_FREQ_CONF` writer"]
pub type W = crate::W<CPU_FREQ_CONF_SPEC>;
#[doc = "Field `CPU_LS_DIV_NUM` reader - Set as one within (0,1,3) to generate clk_cpu drived by clk_hproot. The clk_cpu is div1(default)/div2/div4 of clk_hproot. This field is only avaliable for low-speed clock-source such as XTAL/FOSC, and should be used together with PCR_AHB_LS_DIV_NUM."]
pub type CPU_LS_DIV_NUM_R = crate::FieldReader;
#[doc = "Field `CPU_LS_DIV_NUM` writer - Set as one within (0,1,3) to generate clk_cpu drived by clk_hproot. The clk_cpu is div1(default)/div2/div4 of clk_hproot. This field is only avaliable for low-speed clock-source such as XTAL/FOSC, and should be used together with PCR_AHB_LS_DIV_NUM."]
pub type CPU_LS_DIV_NUM_W<'a, REG> = crate::FieldWriter<'a, REG, 8>;
#[doc = "Field `CPU_HS_DIV_NUM` reader - Set as one within (0,1,3) to generate clk_cpu drived by clk_hproot. The clk_cpu is div1(default)/div2/div4 of clk_hproot. This field is only avaliable for high-speed clock-source such as SPLL, and should be used together with PCR_AHB_HS_DIV_NUM."]
pub type CPU_HS_DIV_NUM_R = crate::FieldReader;
#[doc = "Field `CPU_HS_DIV_NUM` writer - Set as one within (0,1,3) to generate clk_cpu drived by clk_hproot. The clk_cpu is div1(default)/div2/div4 of clk_hproot. This field is only avaliable for high-speed clock-source such as SPLL, and should be used together with PCR_AHB_HS_DIV_NUM."]
pub type CPU_HS_DIV_NUM_W<'a, REG> = crate::FieldWriter<'a, REG, 8>;
#[doc = "Field `CPU_HS_120M_FORCE` reader - Given that PCR_CPU_HS_DIV_NUM is 0, set this field as 1 to force clk_cpu at 120MHz. Only avaliable when PCR_CPU_HS_DIV_NUM is 0 and clk_cpu is driven by SPLL."]
pub type CPU_HS_120M_FORCE_R = crate::BitReader;
#[doc = "Field `CPU_HS_120M_FORCE` writer - Given that PCR_CPU_HS_DIV_NUM is 0, set this field as 1 to force clk_cpu at 120MHz. Only avaliable when PCR_CPU_HS_DIV_NUM is 0 and clk_cpu is driven by SPLL."]
pub type CPU_HS_120M_FORCE_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bits 0:7 - Set as one within (0,1,3) to generate clk_cpu drived by clk_hproot. The clk_cpu is div1(default)/div2/div4 of clk_hproot. This field is only avaliable for low-speed clock-source such as XTAL/FOSC, and should be used together with PCR_AHB_LS_DIV_NUM."]
    #[inline(always)]
    pub fn cpu_ls_div_num(&self) -> CPU_LS_DIV_NUM_R {
        CPU_LS_DIV_NUM_R::new((self.bits & 0xff) as u8)
    }
    #[doc = "Bits 8:15 - Set as one within (0,1,3) to generate clk_cpu drived by clk_hproot. The clk_cpu is div1(default)/div2/div4 of clk_hproot. This field is only avaliable for high-speed clock-source such as SPLL, and should be used together with PCR_AHB_HS_DIV_NUM."]
    #[inline(always)]
    pub fn cpu_hs_div_num(&self) -> CPU_HS_DIV_NUM_R {
        CPU_HS_DIV_NUM_R::new(((self.bits >> 8) & 0xff) as u8)
    }
    #[doc = "Bit 16 - Given that PCR_CPU_HS_DIV_NUM is 0, set this field as 1 to force clk_cpu at 120MHz. Only avaliable when PCR_CPU_HS_DIV_NUM is 0 and clk_cpu is driven by SPLL."]
    #[inline(always)]
    pub fn cpu_hs_120m_force(&self) -> CPU_HS_120M_FORCE_R {
        CPU_HS_120M_FORCE_R::new(((self.bits >> 16) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("CPU_FREQ_CONF")
            .field("cpu_ls_div_num", &self.cpu_ls_div_num())
            .field("cpu_hs_div_num", &self.cpu_hs_div_num())
            .field("cpu_hs_120m_force", &self.cpu_hs_120m_force())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:7 - Set as one within (0,1,3) to generate clk_cpu drived by clk_hproot. The clk_cpu is div1(default)/div2/div4 of clk_hproot. This field is only avaliable for low-speed clock-source such as XTAL/FOSC, and should be used together with PCR_AHB_LS_DIV_NUM."]
    #[inline(always)]
    pub fn cpu_ls_div_num(&mut self) -> CPU_LS_DIV_NUM_W<'_, CPU_FREQ_CONF_SPEC> {
        CPU_LS_DIV_NUM_W::new(self, 0)
    }
    #[doc = "Bits 8:15 - Set as one within (0,1,3) to generate clk_cpu drived by clk_hproot. The clk_cpu is div1(default)/div2/div4 of clk_hproot. This field is only avaliable for high-speed clock-source such as SPLL, and should be used together with PCR_AHB_HS_DIV_NUM."]
    #[inline(always)]
    pub fn cpu_hs_div_num(&mut self) -> CPU_HS_DIV_NUM_W<'_, CPU_FREQ_CONF_SPEC> {
        CPU_HS_DIV_NUM_W::new(self, 8)
    }
    #[doc = "Bit 16 - Given that PCR_CPU_HS_DIV_NUM is 0, set this field as 1 to force clk_cpu at 120MHz. Only avaliable when PCR_CPU_HS_DIV_NUM is 0 and clk_cpu is driven by SPLL."]
    #[inline(always)]
    pub fn cpu_hs_120m_force(&mut self) -> CPU_HS_120M_FORCE_W<'_, CPU_FREQ_CONF_SPEC> {
        CPU_HS_120M_FORCE_W::new(self, 16)
    }
}
#[doc = "CPU_FREQ configuration register\n\nYou can [`read`](crate::Reg::read) this register and get [`cpu_freq_conf::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`cpu_freq_conf::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct CPU_FREQ_CONF_SPEC;
impl crate::RegisterSpec for CPU_FREQ_CONF_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`cpu_freq_conf::R`](R) reader structure"]
impl crate::Readable for CPU_FREQ_CONF_SPEC {}
#[doc = "`write(|w| ..)` method takes [`cpu_freq_conf::W`](W) writer structure"]
impl crate::Writable for CPU_FREQ_CONF_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets CPU_FREQ_CONF to value 0"]
impl crate::Resettable for CPU_FREQ_CONF_SPEC {}
