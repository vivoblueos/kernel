#[doc = "Register `COMD%s` reader"]
pub type R = crate::R<COMD_SPEC>;
#[doc = "Register `COMD%s` writer"]
pub type W = crate::W<COMD_SPEC>;
#[doc = "Field `BYTE_NUM` reader - Number of bytes to be sent or received for command %s."]
pub type BYTE_NUM_R = crate::FieldReader;
#[doc = "Field `BYTE_NUM` writer - Number of bytes to be sent or received for command %s."]
pub type BYTE_NUM_W<'a, REG> = crate::FieldWriter<'a, REG, 8>;
#[doc = "Field `ACK_CHECK_EN` reader - Acknowledge check enable for command %s."]
pub type ACK_CHECK_EN_R = crate::BitReader;
#[doc = "Field `ACK_CHECK_EN` writer - Acknowledge check enable for command %s."]
pub type ACK_CHECK_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ACK_EXP` reader - Acknowledge expected for command %s."]
pub type ACK_EXP_R = crate::BitReader;
#[doc = "Field `ACK_EXP` writer - Acknowledge expected for command %s."]
pub type ACK_EXP_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ACK_VALUE` reader - Acknowledge value for command %s."]
pub type ACK_VALUE_R = crate::BitReader;
#[doc = "Field `ACK_VALUE` writer - Acknowledge value for command %s."]
pub type ACK_VALUE_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Opcode part of command %s.\n\nValue on reset: 0"]
#[cfg_attr(feature = "defmt", derive(defmt::Format))]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u8)]
pub enum OPCODE {
    #[doc = "1: WRITE opcode"]
    Write  = 1,
    #[doc = "2: STOP opcode"]
    Stop   = 2,
    #[doc = "3: READ opcode"]
    Read   = 3,
    #[doc = "4: END opcode"]
    End    = 4,
    #[doc = "6: RSTART opcode"]
    Rstart = 6,
}
impl From<OPCODE> for u8 {
    #[inline(always)]
    fn from(variant: OPCODE) -> Self {
        variant as _
    }
}
impl crate::FieldSpec for OPCODE {
    type Ux = u8;
}
impl crate::IsEnum for OPCODE {}
#[doc = "Field `OPCODE` reader - Opcode part of command %s."]
pub type OPCODE_R = crate::FieldReader<OPCODE>;
impl OPCODE_R {
    #[doc = "Get enumerated values variant"]
    #[inline(always)]
    pub const fn variant(&self) -> Option<OPCODE> {
        match self.bits {
            1 => Some(OPCODE::Write),
            2 => Some(OPCODE::Stop),
            3 => Some(OPCODE::Read),
            4 => Some(OPCODE::End),
            6 => Some(OPCODE::Rstart),
            _ => None,
        }
    }
    #[doc = "WRITE opcode"]
    #[inline(always)]
    pub fn is_write(&self) -> bool {
        *self == OPCODE::Write
    }
    #[doc = "STOP opcode"]
    #[inline(always)]
    pub fn is_stop(&self) -> bool {
        *self == OPCODE::Stop
    }
    #[doc = "READ opcode"]
    #[inline(always)]
    pub fn is_read(&self) -> bool {
        *self == OPCODE::Read
    }
    #[doc = "END opcode"]
    #[inline(always)]
    pub fn is_end(&self) -> bool {
        *self == OPCODE::End
    }
    #[doc = "RSTART opcode"]
    #[inline(always)]
    pub fn is_rstart(&self) -> bool {
        *self == OPCODE::Rstart
    }
}
#[doc = "Field `OPCODE` writer - Opcode part of command %s."]
pub type OPCODE_W<'a, REG> = crate::FieldWriter<'a, REG, 3, OPCODE>;
impl<'a, REG> OPCODE_W<'a, REG>
where
    REG: crate::Writable + crate::RegisterSpec,
    REG::Ux: From<u8>,
{
    #[doc = "WRITE opcode"]
    #[inline(always)]
    pub fn write(self) -> &'a mut crate::W<REG> {
        self.variant(OPCODE::Write)
    }
    #[doc = "STOP opcode"]
    #[inline(always)]
    pub fn stop(self) -> &'a mut crate::W<REG> {
        self.variant(OPCODE::Stop)
    }
    #[doc = "READ opcode"]
    #[inline(always)]
    pub fn read(self) -> &'a mut crate::W<REG> {
        self.variant(OPCODE::Read)
    }
    #[doc = "END opcode"]
    #[inline(always)]
    pub fn end(self) -> &'a mut crate::W<REG> {
        self.variant(OPCODE::End)
    }
    #[doc = "RSTART opcode"]
    #[inline(always)]
    pub fn rstart(self) -> &'a mut crate::W<REG> {
        self.variant(OPCODE::Rstart)
    }
}
#[doc = "Field `COMMAND_DONE` reader - When command 0 is done in I2C Master mode, this bit changes to high level."]
pub type COMMAND_DONE_R = crate::BitReader;
#[doc = "Field `COMMAND_DONE` writer - When command 0 is done in I2C Master mode, this bit changes to high level."]
pub type COMMAND_DONE_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bits 0:7 - Number of bytes to be sent or received for command %s."]
    #[inline(always)]
    pub fn byte_num(&self) -> BYTE_NUM_R {
        BYTE_NUM_R::new((self.bits & 0xff) as u8)
    }
    #[doc = "Bit 8 - Acknowledge check enable for command %s."]
    #[inline(always)]
    pub fn ack_check_en(&self) -> ACK_CHECK_EN_R {
        ACK_CHECK_EN_R::new(((self.bits >> 8) & 1) != 0)
    }
    #[doc = "Bit 9 - Acknowledge expected for command %s."]
    #[inline(always)]
    pub fn ack_exp(&self) -> ACK_EXP_R {
        ACK_EXP_R::new(((self.bits >> 9) & 1) != 0)
    }
    #[doc = "Bit 10 - Acknowledge value for command %s."]
    #[inline(always)]
    pub fn ack_value(&self) -> ACK_VALUE_R {
        ACK_VALUE_R::new(((self.bits >> 10) & 1) != 0)
    }
    #[doc = "Bits 11:13 - Opcode part of command %s."]
    #[inline(always)]
    pub fn opcode(&self) -> OPCODE_R {
        OPCODE_R::new(((self.bits >> 11) & 7) as u8)
    }
    #[doc = "Bit 31 - When command 0 is done in I2C Master mode, this bit changes to high level."]
    #[inline(always)]
    pub fn command_done(&self) -> COMMAND_DONE_R {
        COMMAND_DONE_R::new(((self.bits >> 31) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("COMD")
            .field("command_done", &self.command_done())
            .field("opcode", &self.opcode())
            .field("ack_value", &self.ack_value())
            .field("ack_exp", &self.ack_exp())
            .field("ack_check_en", &self.ack_check_en())
            .field("byte_num", &self.byte_num())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:7 - Number of bytes to be sent or received for command %s."]
    #[inline(always)]
    pub fn byte_num(&mut self) -> BYTE_NUM_W<'_, COMD_SPEC> {
        BYTE_NUM_W::new(self, 0)
    }
    #[doc = "Bit 8 - Acknowledge check enable for command %s."]
    #[inline(always)]
    pub fn ack_check_en(&mut self) -> ACK_CHECK_EN_W<'_, COMD_SPEC> {
        ACK_CHECK_EN_W::new(self, 8)
    }
    #[doc = "Bit 9 - Acknowledge expected for command %s."]
    #[inline(always)]
    pub fn ack_exp(&mut self) -> ACK_EXP_W<'_, COMD_SPEC> {
        ACK_EXP_W::new(self, 9)
    }
    #[doc = "Bit 10 - Acknowledge value for command %s."]
    #[inline(always)]
    pub fn ack_value(&mut self) -> ACK_VALUE_W<'_, COMD_SPEC> {
        ACK_VALUE_W::new(self, 10)
    }
    #[doc = "Bits 11:13 - Opcode part of command %s."]
    #[inline(always)]
    pub fn opcode(&mut self) -> OPCODE_W<'_, COMD_SPEC> {
        OPCODE_W::new(self, 11)
    }
    #[doc = "Bit 31 - When command 0 is done in I2C Master mode, this bit changes to high level."]
    #[inline(always)]
    pub fn command_done(&mut self) -> COMMAND_DONE_W<'_, COMD_SPEC> {
        COMMAND_DONE_W::new(self, 31)
    }
}
#[doc = "I2C command register %s\n\nYou can [`read`](crate::Reg::read) this register and get [`comd::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`comd::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct COMD_SPEC;
impl crate::RegisterSpec for COMD_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`comd::R`](R) reader structure"]
impl crate::Readable for COMD_SPEC {}
#[doc = "`write(|w| ..)` method takes [`comd::W`](W) writer structure"]
impl crate::Writable for COMD_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets COMD%s to value 0"]
impl crate::Resettable for COMD_SPEC {}
