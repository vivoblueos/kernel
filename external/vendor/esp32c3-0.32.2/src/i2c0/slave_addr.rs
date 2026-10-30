#[doc = "Register `SLAVE_ADDR` reader"]
pub type R = crate::R<SLAVE_ADDR_SPEC>;
#[doc = "Register `SLAVE_ADDR` writer"]
pub type W = crate::W<SLAVE_ADDR_SPEC>;
#[doc = "Field `SLAVE_ADDR` reader - reg_slave_addr"]
pub type SLAVE_ADDR_R = crate::FieldReader<u16>;
#[doc = "Field `SLAVE_ADDR` writer - reg_slave_addr"]
pub type SLAVE_ADDR_W<'a, REG> = crate::FieldWriter<'a, REG, 15, u16>;
#[doc = "Field `ADDR_10BIT_EN` reader - reg_addr_10bit_en"]
pub type ADDR_10BIT_EN_R = crate::BitReader;
#[doc = "Field `ADDR_10BIT_EN` writer - reg_addr_10bit_en"]
pub type ADDR_10BIT_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bits 0:14 - reg_slave_addr"]
    #[inline(always)]
    pub fn slave_addr(&self) -> SLAVE_ADDR_R {
        SLAVE_ADDR_R::new((self.bits & 0x7fff) as u16)
    }
    #[doc = "Bit 31 - reg_addr_10bit_en"]
    #[inline(always)]
    pub fn addr_10bit_en(&self) -> ADDR_10BIT_EN_R {
        ADDR_10BIT_EN_R::new(((self.bits >> 31) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("SLAVE_ADDR")
            .field("slave_addr", &self.slave_addr())
            .field("addr_10bit_en", &self.addr_10bit_en())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:14 - reg_slave_addr"]
    #[inline(always)]
    pub fn slave_addr(&mut self) -> SLAVE_ADDR_W<'_, SLAVE_ADDR_SPEC> {
        SLAVE_ADDR_W::new(self, 0)
    }
    #[doc = "Bit 31 - reg_addr_10bit_en"]
    #[inline(always)]
    pub fn addr_10bit_en(&mut self) -> ADDR_10BIT_EN_W<'_, SLAVE_ADDR_SPEC> {
        ADDR_10BIT_EN_W::new(self, 31)
    }
}
#[doc = "I2C_SLAVE_ADDR_REG\n\nYou can [`read`](crate::Reg::read) this register and get [`slave_addr::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`slave_addr::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct SLAVE_ADDR_SPEC;
impl crate::RegisterSpec for SLAVE_ADDR_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`slave_addr::R`](R) reader structure"]
impl crate::Readable for SLAVE_ADDR_SPEC {}
#[doc = "`write(|w| ..)` method takes [`slave_addr::W`](W) writer structure"]
impl crate::Writable for SLAVE_ADDR_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets SLAVE_ADDR to value 0"]
impl crate::Resettable for SLAVE_ADDR_SPEC {}
