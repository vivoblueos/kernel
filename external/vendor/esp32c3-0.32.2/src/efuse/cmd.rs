#[doc = "Register `CMD` reader"]
pub type R = crate::R<CMD_SPEC>;
#[doc = "Register `CMD` writer"]
pub type W = crate::W<CMD_SPEC>;
#[doc = "Field `READ_CMD` reader - Set this bit to send read command."]
pub type READ_CMD_R = crate::BitReader;
#[doc = "Field `READ_CMD` writer - Set this bit to send read command."]
pub type READ_CMD_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `PGM_CMD` reader - Set this bit to send programming command."]
pub type PGM_CMD_R = crate::BitReader;
#[doc = "Field `PGM_CMD` writer - Set this bit to send programming command."]
pub type PGM_CMD_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `BLK_NUM` reader - The serial number of the block to be programmed. Value 0-10 corresponds to block number 0-10, respectively."]
pub type BLK_NUM_R = crate::FieldReader;
#[doc = "Field `BLK_NUM` writer - The serial number of the block to be programmed. Value 0-10 corresponds to block number 0-10, respectively."]
pub type BLK_NUM_W<'a, REG> = crate::FieldWriter<'a, REG, 4>;
impl R {
    #[doc = "Bit 0 - Set this bit to send read command."]
    #[inline(always)]
    pub fn read_cmd(&self) -> READ_CMD_R {
        READ_CMD_R::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - Set this bit to send programming command."]
    #[inline(always)]
    pub fn pgm_cmd(&self) -> PGM_CMD_R {
        PGM_CMD_R::new(((self.bits >> 1) & 1) != 0)
    }
    #[doc = "Bits 2:5 - The serial number of the block to be programmed. Value 0-10 corresponds to block number 0-10, respectively."]
    #[inline(always)]
    pub fn blk_num(&self) -> BLK_NUM_R {
        BLK_NUM_R::new(((self.bits >> 2) & 0x0f) as u8)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("CMD")
            .field("read_cmd", &self.read_cmd())
            .field("pgm_cmd", &self.pgm_cmd())
            .field("blk_num", &self.blk_num())
            .finish()
    }
}
impl W {
    #[doc = "Bit 0 - Set this bit to send read command."]
    #[inline(always)]
    pub fn read_cmd(&mut self) -> READ_CMD_W<'_, CMD_SPEC> {
        READ_CMD_W::new(self, 0)
    }
    #[doc = "Bit 1 - Set this bit to send programming command."]
    #[inline(always)]
    pub fn pgm_cmd(&mut self) -> PGM_CMD_W<'_, CMD_SPEC> {
        PGM_CMD_W::new(self, 1)
    }
    #[doc = "Bits 2:5 - The serial number of the block to be programmed. Value 0-10 corresponds to block number 0-10, respectively."]
    #[inline(always)]
    pub fn blk_num(&mut self) -> BLK_NUM_W<'_, CMD_SPEC> {
        BLK_NUM_W::new(self, 2)
    }
}
#[doc = "eFuse command register.\n\nYou can [`read`](crate::Reg::read) this register and get [`cmd::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`cmd::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
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
