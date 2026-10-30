#[doc = "Register `ID` reader"]
pub type R = crate::R<ID_SPEC>;
#[doc = "Register `ID` writer"]
pub type W = crate::W<ID_SPEC>;
#[doc = "Field `ID` reader - This register is used to configure the uart_id."]
pub type ID_R = crate::FieldReader<u32>;
#[doc = "Field `ID` writer - This register is used to configure the uart_id."]
pub type ID_W<'a, REG> = crate::FieldWriter<'a, REG, 30, u32>;
#[doc = "Field `HIGH_SPEED` reader - This bit used to select synchronize mode. 1: Registers are auto synchronized into UART Core clock and UART core should be keep the same with APB clock. 0: After configure registers, software needs to write 1 to UART_REG_UPDATE to synchronize registers."]
pub type HIGH_SPEED_R = crate::BitReader;
#[doc = "Field `HIGH_SPEED` writer - This bit used to select synchronize mode. 1: Registers are auto synchronized into UART Core clock and UART core should be keep the same with APB clock. 0: After configure registers, software needs to write 1 to UART_REG_UPDATE to synchronize registers."]
pub type HIGH_SPEED_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `REG_UPDATE` reader - Software write 1 would synchronize registers into UART Core clock domain and would be cleared by hardware after synchronization is done."]
pub type REG_UPDATE_R = crate::BitReader;
#[doc = "Field `REG_UPDATE` writer - Software write 1 would synchronize registers into UART Core clock domain and would be cleared by hardware after synchronization is done."]
pub type REG_UPDATE_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bits 0:29 - This register is used to configure the uart_id."]
    #[inline(always)]
    pub fn id(&self) -> ID_R {
        ID_R::new(self.bits & 0x3fff_ffff)
    }
    #[doc = "Bit 30 - This bit used to select synchronize mode. 1: Registers are auto synchronized into UART Core clock and UART core should be keep the same with APB clock. 0: After configure registers, software needs to write 1 to UART_REG_UPDATE to synchronize registers."]
    #[inline(always)]
    pub fn high_speed(&self) -> HIGH_SPEED_R {
        HIGH_SPEED_R::new(((self.bits >> 30) & 1) != 0)
    }
    #[doc = "Bit 31 - Software write 1 would synchronize registers into UART Core clock domain and would be cleared by hardware after synchronization is done."]
    #[inline(always)]
    pub fn reg_update(&self) -> REG_UPDATE_R {
        REG_UPDATE_R::new(((self.bits >> 31) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("ID")
            .field("id", &self.id())
            .field("high_speed", &self.high_speed())
            .field("reg_update", &self.reg_update())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:29 - This register is used to configure the uart_id."]
    #[inline(always)]
    pub fn id(&mut self) -> ID_W<'_, ID_SPEC> {
        ID_W::new(self, 0)
    }
    #[doc = "Bit 30 - This bit used to select synchronize mode. 1: Registers are auto synchronized into UART Core clock and UART core should be keep the same with APB clock. 0: After configure registers, software needs to write 1 to UART_REG_UPDATE to synchronize registers."]
    #[inline(always)]
    pub fn high_speed(&mut self) -> HIGH_SPEED_W<'_, ID_SPEC> {
        HIGH_SPEED_W::new(self, 30)
    }
    #[doc = "Bit 31 - Software write 1 would synchronize registers into UART Core clock domain and would be cleared by hardware after synchronization is done."]
    #[inline(always)]
    pub fn reg_update(&mut self) -> REG_UPDATE_W<'_, ID_SPEC> {
        REG_UPDATE_W::new(self, 31)
    }
}
#[doc = "UART ID register\n\nYou can [`read`](crate::Reg::read) this register and get [`id::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`id::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct ID_SPEC;
impl crate::RegisterSpec for ID_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`id::R`](R) reader structure"]
impl crate::Readable for ID_SPEC {}
#[doc = "`write(|w| ..)` method takes [`id::W`](W) writer structure"]
impl crate::Writable for ID_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets ID to value 0x4000_0500"]
impl crate::Resettable for ID_SPEC {
    const RESET_VALUE: u32 = 0x4000_0500;
}
