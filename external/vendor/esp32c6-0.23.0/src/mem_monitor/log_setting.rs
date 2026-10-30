#[doc = "Register `LOG_SETTING` reader"]
pub type R = crate::R<LOG_SETTING_SPEC>;
#[doc = "Register `LOG_SETTING` writer"]
pub type W = crate::W<LOG_SETTING_SPEC>;
#[doc = "Field `LOG_ENA` reader - enable bus log. BIT0: hp-cpu, BIT1: lp-cpu, BIT2: DMA."]
pub type LOG_ENA_R = crate::FieldReader;
#[doc = "Field `LOG_ENA` writer - enable bus log. BIT0: hp-cpu, BIT1: lp-cpu, BIT2: DMA."]
pub type LOG_ENA_W<'a, REG> = crate::FieldWriter<'a, REG, 3>;
#[doc = "Field `LOG_MODE` reader - This field must be onehot. 4'b0001 : WR monitor, 4'b0010: WORD monitor, 4'b0100: HALFWORD monitor, 4'b1000: BYTE monitor."]
pub type LOG_MODE_R = crate::FieldReader;
#[doc = "Field `LOG_MODE` writer - This field must be onehot. 4'b0001 : WR monitor, 4'b0010: WORD monitor, 4'b0100: HALFWORD monitor, 4'b1000: BYTE monitor."]
pub type LOG_MODE_W<'a, REG> = crate::FieldWriter<'a, REG, 4>;
#[doc = "Field `LOG_MEM_LOOP_ENABLE` reader - Set 1 enable mem_loop, it will loop write at the range of MEM_START and MEM_END"]
pub type LOG_MEM_LOOP_ENABLE_R = crate::BitReader;
#[doc = "Field `LOG_MEM_LOOP_ENABLE` writer - Set 1 enable mem_loop, it will loop write at the range of MEM_START and MEM_END"]
pub type LOG_MEM_LOOP_ENABLE_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bits 0:2 - enable bus log. BIT0: hp-cpu, BIT1: lp-cpu, BIT2: DMA."]
    #[inline(always)]
    pub fn log_ena(&self) -> LOG_ENA_R {
        LOG_ENA_R::new((self.bits & 7) as u8)
    }
    #[doc = "Bits 3:6 - This field must be onehot. 4'b0001 : WR monitor, 4'b0010: WORD monitor, 4'b0100: HALFWORD monitor, 4'b1000: BYTE monitor."]
    #[inline(always)]
    pub fn log_mode(&self) -> LOG_MODE_R {
        LOG_MODE_R::new(((self.bits >> 3) & 0x0f) as u8)
    }
    #[doc = "Bit 7 - Set 1 enable mem_loop, it will loop write at the range of MEM_START and MEM_END"]
    #[inline(always)]
    pub fn log_mem_loop_enable(&self) -> LOG_MEM_LOOP_ENABLE_R {
        LOG_MEM_LOOP_ENABLE_R::new(((self.bits >> 7) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("LOG_SETTING")
            .field("log_ena", &self.log_ena())
            .field("log_mode", &self.log_mode())
            .field("log_mem_loop_enable", &self.log_mem_loop_enable())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:2 - enable bus log. BIT0: hp-cpu, BIT1: lp-cpu, BIT2: DMA."]
    #[inline(always)]
    pub fn log_ena(&mut self) -> LOG_ENA_W<'_, LOG_SETTING_SPEC> {
        LOG_ENA_W::new(self, 0)
    }
    #[doc = "Bits 3:6 - This field must be onehot. 4'b0001 : WR monitor, 4'b0010: WORD monitor, 4'b0100: HALFWORD monitor, 4'b1000: BYTE monitor."]
    #[inline(always)]
    pub fn log_mode(&mut self) -> LOG_MODE_W<'_, LOG_SETTING_SPEC> {
        LOG_MODE_W::new(self, 3)
    }
    #[doc = "Bit 7 - Set 1 enable mem_loop, it will loop write at the range of MEM_START and MEM_END"]
    #[inline(always)]
    pub fn log_mem_loop_enable(&mut self) -> LOG_MEM_LOOP_ENABLE_W<'_, LOG_SETTING_SPEC> {
        LOG_MEM_LOOP_ENABLE_W::new(self, 7)
    }
}
#[doc = "log config regsiter\n\nYou can [`read`](crate::Reg::read) this register and get [`log_setting::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`log_setting::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct LOG_SETTING_SPEC;
impl crate::RegisterSpec for LOG_SETTING_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`log_setting::R`](R) reader structure"]
impl crate::Readable for LOG_SETTING_SPEC {}
#[doc = "`write(|w| ..)` method takes [`log_setting::W`](W) writer structure"]
impl crate::Writable for LOG_SETTING_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets LOG_SETTING to value 0x80"]
impl crate::Resettable for LOG_SETTING_SPEC {
    const RESET_VALUE: u32 = 0x80;
}
