#[doc = "Register `FLASH_WAITI_CTRL` reader"]
pub type R = crate::R<FLASH_WAITI_CTRL_SPEC>;
#[doc = "Register `FLASH_WAITI_CTRL` writer"]
pub type W = crate::W<FLASH_WAITI_CTRL_SPEC>;
#[doc = "Field `WAITI_DUMMY` reader - The dummy phase enable when wait flash idle (RDSR)"]
pub type WAITI_DUMMY_R = crate::BitReader;
#[doc = "Field `WAITI_DUMMY` writer - The dummy phase enable when wait flash idle (RDSR)"]
pub type WAITI_DUMMY_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `WAITI_CMD` reader - The command to wait flash idle(RDSR)."]
pub type WAITI_CMD_R = crate::FieldReader;
#[doc = "Field `WAITI_CMD` writer - The command to wait flash idle(RDSR)."]
pub type WAITI_CMD_W<'a, REG> = crate::FieldWriter<'a, REG, 8>;
#[doc = "Field `WAITI_DUMMY_CYCLELEN` reader - The dummy cycle length when wait flash idle(RDSR)."]
pub type WAITI_DUMMY_CYCLELEN_R = crate::FieldReader;
#[doc = "Field `WAITI_DUMMY_CYCLELEN` writer - The dummy cycle length when wait flash idle(RDSR)."]
pub type WAITI_DUMMY_CYCLELEN_W<'a, REG> = crate::FieldWriter<'a, REG, 6>;
impl R {
    #[doc = "Bit 1 - The dummy phase enable when wait flash idle (RDSR)"]
    #[inline(always)]
    pub fn waiti_dummy(&self) -> WAITI_DUMMY_R {
        WAITI_DUMMY_R::new(((self.bits >> 1) & 1) != 0)
    }
    #[doc = "Bits 2:9 - The command to wait flash idle(RDSR)."]
    #[inline(always)]
    pub fn waiti_cmd(&self) -> WAITI_CMD_R {
        WAITI_CMD_R::new(((self.bits >> 2) & 0xff) as u8)
    }
    #[doc = "Bits 10:15 - The dummy cycle length when wait flash idle(RDSR)."]
    #[inline(always)]
    pub fn waiti_dummy_cyclelen(&self) -> WAITI_DUMMY_CYCLELEN_R {
        WAITI_DUMMY_CYCLELEN_R::new(((self.bits >> 10) & 0x3f) as u8)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("FLASH_WAITI_CTRL")
            .field("waiti_dummy", &self.waiti_dummy())
            .field("waiti_cmd", &self.waiti_cmd())
            .field("waiti_dummy_cyclelen", &self.waiti_dummy_cyclelen())
            .finish()
    }
}
impl W {
    #[doc = "Bit 1 - The dummy phase enable when wait flash idle (RDSR)"]
    #[inline(always)]
    pub fn waiti_dummy(&mut self) -> WAITI_DUMMY_W<'_, FLASH_WAITI_CTRL_SPEC> {
        WAITI_DUMMY_W::new(self, 1)
    }
    #[doc = "Bits 2:9 - The command to wait flash idle(RDSR)."]
    #[inline(always)]
    pub fn waiti_cmd(&mut self) -> WAITI_CMD_W<'_, FLASH_WAITI_CTRL_SPEC> {
        WAITI_CMD_W::new(self, 2)
    }
    #[doc = "Bits 10:15 - The dummy cycle length when wait flash idle(RDSR)."]
    #[inline(always)]
    pub fn waiti_dummy_cyclelen(&mut self) -> WAITI_DUMMY_CYCLELEN_W<'_, FLASH_WAITI_CTRL_SPEC> {
        WAITI_DUMMY_CYCLELEN_W::new(self, 10)
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
#[doc = "`reset()` method sets FLASH_WAITI_CTRL to value 0x14"]
impl crate::Resettable for FLASH_WAITI_CTRL_SPEC {
    const RESET_VALUE: u32 = 0x14;
}
