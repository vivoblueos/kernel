#[doc = "Register `FLASH_WAITI_CTRL` reader"]
pub type R = crate::R<FLASH_WAITI_CTRL_SPEC>;
#[doc = "Register `FLASH_WAITI_CTRL` writer"]
pub type W = crate::W<FLASH_WAITI_CTRL_SPEC>;
#[doc = "Field `WAITI_EN` reader - 1: The hardware will wait idle after SE/PP/WRSR automatically, and hardware auto Suspend/Resume can be enabled. 0: The functions of hardware wait idle and auto Suspend/Resume are not supported."]
pub type WAITI_EN_R = crate::BitReader;
#[doc = "Field `WAITI_EN` writer - 1: The hardware will wait idle after SE/PP/WRSR automatically, and hardware auto Suspend/Resume can be enabled. 0: The functions of hardware wait idle and auto Suspend/Resume are not supported."]
pub type WAITI_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `WAITI_DUMMY` reader - The dummy phase enable when wait flash idle (RDSR)"]
pub type WAITI_DUMMY_R = crate::BitReader;
#[doc = "Field `WAITI_DUMMY` writer - The dummy phase enable when wait flash idle (RDSR)"]
pub type WAITI_DUMMY_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `WAITI_ADDR_EN` reader - 1: Output address 0 in RDSR or read SUS command transfer. 0: Do not send out address in RDSR or read SUS command transfer."]
pub type WAITI_ADDR_EN_R = crate::BitReader;
#[doc = "Field `WAITI_ADDR_EN` writer - 1: Output address 0 in RDSR or read SUS command transfer. 0: Do not send out address in RDSR or read SUS command transfer."]
pub type WAITI_ADDR_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `WAITI_ADDR_CYCLELEN` reader - When SPI_MEM_WAITI_ADDR_EN is set, the cycle length of sent out address is (SPI_MEM_WAITI_ADDR_CYCLELEN\\[1:0\\] + 1) SPI bus clock cycles. It is not active when SPI_MEM_WAITI_ADDR_EN is cleared."]
pub type WAITI_ADDR_CYCLELEN_R = crate::FieldReader;
#[doc = "Field `WAITI_ADDR_CYCLELEN` writer - When SPI_MEM_WAITI_ADDR_EN is set, the cycle length of sent out address is (SPI_MEM_WAITI_ADDR_CYCLELEN\\[1:0\\] + 1) SPI bus clock cycles. It is not active when SPI_MEM_WAITI_ADDR_EN is cleared."]
pub type WAITI_ADDR_CYCLELEN_W<'a, REG> = crate::FieldWriter<'a, REG, 2>;
#[doc = "Field `WAITI_CMD_2B` reader - 1:The wait idle command bit length is 16. 0: The wait idle command bit length is 8."]
pub type WAITI_CMD_2B_R = crate::BitReader;
#[doc = "Field `WAITI_CMD_2B` writer - 1:The wait idle command bit length is 16. 0: The wait idle command bit length is 8."]
pub type WAITI_CMD_2B_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `WAITI_DUMMY_CYCLELEN` reader - The dummy cycle length when wait flash idle(RDSR)."]
pub type WAITI_DUMMY_CYCLELEN_R = crate::FieldReader;
#[doc = "Field `WAITI_DUMMY_CYCLELEN` writer - The dummy cycle length when wait flash idle(RDSR)."]
pub type WAITI_DUMMY_CYCLELEN_W<'a, REG> = crate::FieldWriter<'a, REG, 6>;
#[doc = "Field `WAITI_CMD` reader - The command value to wait flash idle(RDSR)."]
pub type WAITI_CMD_R = crate::FieldReader<u16>;
#[doc = "Field `WAITI_CMD` writer - The command value to wait flash idle(RDSR)."]
pub type WAITI_CMD_W<'a, REG> = crate::FieldWriter<'a, REG, 16, u16>;
impl R {
    #[doc = "Bit 0 - 1: The hardware will wait idle after SE/PP/WRSR automatically, and hardware auto Suspend/Resume can be enabled. 0: The functions of hardware wait idle and auto Suspend/Resume are not supported."]
    #[inline(always)]
    pub fn waiti_en(&self) -> WAITI_EN_R {
        WAITI_EN_R::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - The dummy phase enable when wait flash idle (RDSR)"]
    #[inline(always)]
    pub fn waiti_dummy(&self) -> WAITI_DUMMY_R {
        WAITI_DUMMY_R::new(((self.bits >> 1) & 1) != 0)
    }
    #[doc = "Bit 2 - 1: Output address 0 in RDSR or read SUS command transfer. 0: Do not send out address in RDSR or read SUS command transfer."]
    #[inline(always)]
    pub fn waiti_addr_en(&self) -> WAITI_ADDR_EN_R {
        WAITI_ADDR_EN_R::new(((self.bits >> 2) & 1) != 0)
    }
    #[doc = "Bits 3:4 - When SPI_MEM_WAITI_ADDR_EN is set, the cycle length of sent out address is (SPI_MEM_WAITI_ADDR_CYCLELEN\\[1:0\\] + 1) SPI bus clock cycles. It is not active when SPI_MEM_WAITI_ADDR_EN is cleared."]
    #[inline(always)]
    pub fn waiti_addr_cyclelen(&self) -> WAITI_ADDR_CYCLELEN_R {
        WAITI_ADDR_CYCLELEN_R::new(((self.bits >> 3) & 3) as u8)
    }
    #[doc = "Bit 9 - 1:The wait idle command bit length is 16. 0: The wait idle command bit length is 8."]
    #[inline(always)]
    pub fn waiti_cmd_2b(&self) -> WAITI_CMD_2B_R {
        WAITI_CMD_2B_R::new(((self.bits >> 9) & 1) != 0)
    }
    #[doc = "Bits 10:15 - The dummy cycle length when wait flash idle(RDSR)."]
    #[inline(always)]
    pub fn waiti_dummy_cyclelen(&self) -> WAITI_DUMMY_CYCLELEN_R {
        WAITI_DUMMY_CYCLELEN_R::new(((self.bits >> 10) & 0x3f) as u8)
    }
    #[doc = "Bits 16:31 - The command value to wait flash idle(RDSR)."]
    #[inline(always)]
    pub fn waiti_cmd(&self) -> WAITI_CMD_R {
        WAITI_CMD_R::new(((self.bits >> 16) & 0xffff) as u16)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("FLASH_WAITI_CTRL")
            .field("waiti_en", &self.waiti_en())
            .field("waiti_dummy", &self.waiti_dummy())
            .field("waiti_addr_en", &self.waiti_addr_en())
            .field("waiti_addr_cyclelen", &self.waiti_addr_cyclelen())
            .field("waiti_cmd_2b", &self.waiti_cmd_2b())
            .field("waiti_dummy_cyclelen", &self.waiti_dummy_cyclelen())
            .field("waiti_cmd", &self.waiti_cmd())
            .finish()
    }
}
impl W {
    #[doc = "Bit 0 - 1: The hardware will wait idle after SE/PP/WRSR automatically, and hardware auto Suspend/Resume can be enabled. 0: The functions of hardware wait idle and auto Suspend/Resume are not supported."]
    #[inline(always)]
    pub fn waiti_en(&mut self) -> WAITI_EN_W<'_, FLASH_WAITI_CTRL_SPEC> {
        WAITI_EN_W::new(self, 0)
    }
    #[doc = "Bit 1 - The dummy phase enable when wait flash idle (RDSR)"]
    #[inline(always)]
    pub fn waiti_dummy(&mut self) -> WAITI_DUMMY_W<'_, FLASH_WAITI_CTRL_SPEC> {
        WAITI_DUMMY_W::new(self, 1)
    }
    #[doc = "Bit 2 - 1: Output address 0 in RDSR or read SUS command transfer. 0: Do not send out address in RDSR or read SUS command transfer."]
    #[inline(always)]
    pub fn waiti_addr_en(&mut self) -> WAITI_ADDR_EN_W<'_, FLASH_WAITI_CTRL_SPEC> {
        WAITI_ADDR_EN_W::new(self, 2)
    }
    #[doc = "Bits 3:4 - When SPI_MEM_WAITI_ADDR_EN is set, the cycle length of sent out address is (SPI_MEM_WAITI_ADDR_CYCLELEN\\[1:0\\] + 1) SPI bus clock cycles. It is not active when SPI_MEM_WAITI_ADDR_EN is cleared."]
    #[inline(always)]
    pub fn waiti_addr_cyclelen(&mut self) -> WAITI_ADDR_CYCLELEN_W<'_, FLASH_WAITI_CTRL_SPEC> {
        WAITI_ADDR_CYCLELEN_W::new(self, 3)
    }
    #[doc = "Bit 9 - 1:The wait idle command bit length is 16. 0: The wait idle command bit length is 8."]
    #[inline(always)]
    pub fn waiti_cmd_2b(&mut self) -> WAITI_CMD_2B_W<'_, FLASH_WAITI_CTRL_SPEC> {
        WAITI_CMD_2B_W::new(self, 9)
    }
    #[doc = "Bits 10:15 - The dummy cycle length when wait flash idle(RDSR)."]
    #[inline(always)]
    pub fn waiti_dummy_cyclelen(&mut self) -> WAITI_DUMMY_CYCLELEN_W<'_, FLASH_WAITI_CTRL_SPEC> {
        WAITI_DUMMY_CYCLELEN_W::new(self, 10)
    }
    #[doc = "Bits 16:31 - The command value to wait flash idle(RDSR)."]
    #[inline(always)]
    pub fn waiti_cmd(&mut self) -> WAITI_CMD_W<'_, FLASH_WAITI_CTRL_SPEC> {
        WAITI_CMD_W::new(self, 16)
    }
}
#[doc = "SPI1 wait idle control register\n\nYou can [`read`](crate::Reg::read) this register and get [`flash_waiti_ctrl::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`flash_waiti_ctrl::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct FLASH_WAITI_CTRL_SPEC;
impl crate::RegisterSpec for FLASH_WAITI_CTRL_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`flash_waiti_ctrl::R`](R) reader structure"]
impl crate::Readable for FLASH_WAITI_CTRL_SPEC {}
#[doc = "`write(|w| ..)` method takes [`flash_waiti_ctrl::W`](W) writer structure"]
impl crate::Writable for FLASH_WAITI_CTRL_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets FLASH_WAITI_CTRL to value 0x0005_0001"]
impl crate::Resettable for FLASH_WAITI_CTRL_SPEC {
    const RESET_VALUE: u32 = 0x0005_0001;
}
