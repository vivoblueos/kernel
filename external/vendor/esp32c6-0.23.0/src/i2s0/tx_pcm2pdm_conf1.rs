#[doc = "Register `TX_PCM2PDM_CONF1` reader"]
pub type R = crate::R<TX_PCM2PDM_CONF1_SPEC>;
#[doc = "Register `TX_PCM2PDM_CONF1` writer"]
pub type W = crate::W<TX_PCM2PDM_CONF1_SPEC>;
#[doc = "Field `TX_PDM_FP` reader - I2S TX PDM Fp"]
pub type TX_PDM_FP_R = crate::FieldReader<u16>;
#[doc = "Field `TX_PDM_FP` writer - I2S TX PDM Fp"]
pub type TX_PDM_FP_W<'a, REG> = crate::FieldWriter<'a, REG, 10, u16>;
#[doc = "Field `TX_PDM_FS` reader - I2S TX PDM Fs"]
pub type TX_PDM_FS_R = crate::FieldReader<u16>;
#[doc = "Field `TX_PDM_FS` writer - I2S TX PDM Fs"]
pub type TX_PDM_FS_W<'a, REG> = crate::FieldWriter<'a, REG, 10, u16>;
#[doc = "Field `TX_IIR_HP_MULT12_5` reader - The fourth parameter of PDM TX IIR_HP filter stage 2 is (504 + I2S_TX_IIR_HP_MULT12_5\\[2:0\\])"]
pub type TX_IIR_HP_MULT12_5_R = crate::FieldReader;
#[doc = "Field `TX_IIR_HP_MULT12_5` writer - The fourth parameter of PDM TX IIR_HP filter stage 2 is (504 + I2S_TX_IIR_HP_MULT12_5\\[2:0\\])"]
pub type TX_IIR_HP_MULT12_5_W<'a, REG> = crate::FieldWriter<'a, REG, 3>;
#[doc = "Field `TX_IIR_HP_MULT12_0` reader - The fourth parameter of PDM TX IIR_HP filter stage 1 is (504 + I2S_TX_IIR_HP_MULT12_0\\[2:0\\])"]
pub type TX_IIR_HP_MULT12_0_R = crate::FieldReader;
#[doc = "Field `TX_IIR_HP_MULT12_0` writer - The fourth parameter of PDM TX IIR_HP filter stage 1 is (504 + I2S_TX_IIR_HP_MULT12_0\\[2:0\\])"]
pub type TX_IIR_HP_MULT12_0_W<'a, REG> = crate::FieldWriter<'a, REG, 3>;
impl R {
    #[doc = "Bits 0:9 - I2S TX PDM Fp"]
    #[inline(always)]
    pub fn tx_pdm_fp(&self) -> TX_PDM_FP_R {
        TX_PDM_FP_R::new((self.bits & 0x03ff) as u16)
    }
    #[doc = "Bits 10:19 - I2S TX PDM Fs"]
    #[inline(always)]
    pub fn tx_pdm_fs(&self) -> TX_PDM_FS_R {
        TX_PDM_FS_R::new(((self.bits >> 10) & 0x03ff) as u16)
    }
    #[doc = "Bits 20:22 - The fourth parameter of PDM TX IIR_HP filter stage 2 is (504 + I2S_TX_IIR_HP_MULT12_5\\[2:0\\])"]
    #[inline(always)]
    pub fn tx_iir_hp_mult12_5(&self) -> TX_IIR_HP_MULT12_5_R {
        TX_IIR_HP_MULT12_5_R::new(((self.bits >> 20) & 7) as u8)
    }
    #[doc = "Bits 23:25 - The fourth parameter of PDM TX IIR_HP filter stage 1 is (504 + I2S_TX_IIR_HP_MULT12_0\\[2:0\\])"]
    #[inline(always)]
    pub fn tx_iir_hp_mult12_0(&self) -> TX_IIR_HP_MULT12_0_R {
        TX_IIR_HP_MULT12_0_R::new(((self.bits >> 23) & 7) as u8)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("TX_PCM2PDM_CONF1")
            .field("tx_pdm_fp", &self.tx_pdm_fp())
            .field("tx_pdm_fs", &self.tx_pdm_fs())
            .field("tx_iir_hp_mult12_5", &self.tx_iir_hp_mult12_5())
            .field("tx_iir_hp_mult12_0", &self.tx_iir_hp_mult12_0())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:9 - I2S TX PDM Fp"]
    #[inline(always)]
    pub fn tx_pdm_fp(&mut self) -> TX_PDM_FP_W<'_, TX_PCM2PDM_CONF1_SPEC> {
        TX_PDM_FP_W::new(self, 0)
    }
    #[doc = "Bits 10:19 - I2S TX PDM Fs"]
    #[inline(always)]
    pub fn tx_pdm_fs(&mut self) -> TX_PDM_FS_W<'_, TX_PCM2PDM_CONF1_SPEC> {
        TX_PDM_FS_W::new(self, 10)
    }
    #[doc = "Bits 20:22 - The fourth parameter of PDM TX IIR_HP filter stage 2 is (504 + I2S_TX_IIR_HP_MULT12_5\\[2:0\\])"]
    #[inline(always)]
    pub fn tx_iir_hp_mult12_5(&mut self) -> TX_IIR_HP_MULT12_5_W<'_, TX_PCM2PDM_CONF1_SPEC> {
        TX_IIR_HP_MULT12_5_W::new(self, 20)
    }
    #[doc = "Bits 23:25 - The fourth parameter of PDM TX IIR_HP filter stage 1 is (504 + I2S_TX_IIR_HP_MULT12_0\\[2:0\\])"]
    #[inline(always)]
    pub fn tx_iir_hp_mult12_0(&mut self) -> TX_IIR_HP_MULT12_0_W<'_, TX_PCM2PDM_CONF1_SPEC> {
        TX_IIR_HP_MULT12_0_W::new(self, 23)
    }
}
#[doc = "I2S TX PCM2PDM configuration register\n\nYou can [`read`](crate::Reg::read) this register and get [`tx_pcm2pdm_conf1::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`tx_pcm2pdm_conf1::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct TX_PCM2PDM_CONF1_SPEC;
impl crate::RegisterSpec for TX_PCM2PDM_CONF1_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`tx_pcm2pdm_conf1::R`](R) reader structure"]
impl crate::Readable for TX_PCM2PDM_CONF1_SPEC {}
#[doc = "`write(|w| ..)` method takes [`tx_pcm2pdm_conf1::W`](W) writer structure"]
impl crate::Writable for TX_PCM2PDM_CONF1_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets TX_PCM2PDM_CONF1 to value 0x03f7_83c0"]
impl crate::Resettable for TX_PCM2PDM_CONF1_SPEC {
    const RESET_VALUE: u32 = 0x03f7_83c0;
}
