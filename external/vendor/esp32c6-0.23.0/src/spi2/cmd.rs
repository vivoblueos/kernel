#[doc = "Register `CMD` reader"]
pub type R = crate::R<CMD_SPEC>;
#[doc = "Register `CMD` writer"]
pub type W = crate::W<CMD_SPEC>;
#[doc = "Field `CONF_BITLEN` reader - Define the APB cycles of SPI_CONF state. Can be configured in CONF state."]
pub type CONF_BITLEN_R = crate::FieldReader<u32>;
#[doc = "Field `CONF_BITLEN` writer - Define the APB cycles of SPI_CONF state. Can be configured in CONF state."]
pub type CONF_BITLEN_W<'a, REG> = crate::FieldWriter<'a, REG, 18, u32>;
#[doc = "Field `UPDATE` reader - Set this bit to synchronize SPI registers from APB clock domain into SPI module clock domain, which is only used in SPI master mode."]
pub type UPDATE_R = crate::BitReader;
#[doc = "Field `UPDATE` writer - Set this bit to synchronize SPI registers from APB clock domain into SPI module clock domain, which is only used in SPI master mode."]
pub type UPDATE_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `USR` reader - User define command enable. An operation will be triggered when the bit is set. The bit will be cleared once the operation done.1: enable 0: disable. Can not be changed by CONF_buf."]
pub type USR_R = crate::BitReader;
#[doc = "Field `USR` writer - User define command enable. An operation will be triggered when the bit is set. The bit will be cleared once the operation done.1: enable 0: disable. Can not be changed by CONF_buf."]
pub type USR_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bits 0:17 - Define the APB cycles of SPI_CONF state. Can be configured in CONF state."]
    #[inline(always)]
    pub fn conf_bitlen(&self) -> CONF_BITLEN_R {
        CONF_BITLEN_R::new(self.bits & 0x0003_ffff)
    }
    #[doc = "Bit 23 - Set this bit to synchronize SPI registers from APB clock domain into SPI module clock domain, which is only used in SPI master mode."]
    #[inline(always)]
    pub fn update(&self) -> UPDATE_R {
        UPDATE_R::new(((self.bits >> 23) & 1) != 0)
    }
    #[doc = "Bit 24 - User define command enable. An operation will be triggered when the bit is set. The bit will be cleared once the operation done.1: enable 0: disable. Can not be changed by CONF_buf."]
    #[inline(always)]
    pub fn usr(&self) -> USR_R {
        USR_R::new(((self.bits >> 24) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("CMD")
            .field("conf_bitlen", &self.conf_bitlen())
            .field("update", &self.update())
            .field("usr", &self.usr())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:17 - Define the APB cycles of SPI_CONF state. Can be configured in CONF state."]
    #[inline(always)]
    pub fn conf_bitlen(&mut self) -> CONF_BITLEN_W<'_, CMD_SPEC> {
        CONF_BITLEN_W::new(self, 0)
    }
    #[doc = "Bit 23 - Set this bit to synchronize SPI registers from APB clock domain into SPI module clock domain, which is only used in SPI master mode."]
    #[inline(always)]
    pub fn update(&mut self) -> UPDATE_W<'_, CMD_SPEC> {
        UPDATE_W::new(self, 23)
    }
    #[doc = "Bit 24 - User define command enable. An operation will be triggered when the bit is set. The bit will be cleared once the operation done.1: enable 0: disable. Can not be changed by CONF_buf."]
    #[inline(always)]
    pub fn usr(&mut self) -> USR_W<'_, CMD_SPEC> {
        USR_W::new(self, 24)
    }
}
#[doc = "Command control register\n\nYou can [`read`](crate::Reg::read) this register and get [`cmd::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`cmd::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct CMD_SPEC;
impl crate::RegisterSpec for CMD_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`cmd::R`](R) reader structure"]
impl crate::Readable for CMD_SPEC {}
#[doc = "`write(|w| ..)` method takes [`cmd::W`](W) writer structure"]
impl crate::Writable for CMD_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets CMD to value 0"]
impl crate::Resettable for CMD_SPEC {}
