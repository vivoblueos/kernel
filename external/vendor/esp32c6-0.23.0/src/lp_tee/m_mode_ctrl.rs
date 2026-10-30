#[doc = "Register `M%s_MODE_CTRL` reader"]
pub type R = crate::R<M_MODE_CTRL_SPEC>;
#[doc = "Register `M%s_MODE_CTRL` writer"]
pub type W = crate::W<M_MODE_CTRL_SPEC>;
#[doc = "M0 security level mode: 2'd3: ree_mode2. 2'd2: ree_mode1. 2'd1: ree_mode0. 2'd0: tee_mode\n\nValue on reset: 3"]
#[cfg_attr(feature = "defmt", derive(defmt::Format))]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u8)]
pub enum SECURITY_MODE {
    #[doc = "0: Tee mode"]
    Tee  = 0,
    #[doc = "1: Ree0 mode"]
    Ree0 = 1,
    #[doc = "2: Ree1 mode"]
    Ree1 = 2,
    #[doc = "3: Ree2 mode"]
    Ree2 = 3,
}
impl From<SECURITY_MODE> for u8 {
    #[inline(always)]
    fn from(variant: SECURITY_MODE) -> Self {
        variant as _
    }
}
impl crate::FieldSpec for SECURITY_MODE {
    type Ux = u8;
}
impl crate::IsEnum for SECURITY_MODE {}
#[doc = "Field `MODE` reader - M0 security level mode: 2'd3: ree_mode2. 2'd2: ree_mode1. 2'd1: ree_mode0. 2'd0: tee_mode"]
pub type MODE_R = crate::FieldReader<SECURITY_MODE>;
impl MODE_R {
    #[doc = "Get enumerated values variant"]
    #[inline(always)]
    pub const fn variant(&self) -> SECURITY_MODE {
        match self.bits {
            0 => SECURITY_MODE::Tee,
            1 => SECURITY_MODE::Ree0,
            2 => SECURITY_MODE::Ree1,
            3 => SECURITY_MODE::Ree2,
            _ => unreachable!(),
        }
    }
    #[doc = "Tee mode"]
    #[inline(always)]
    pub fn is_tee(&self) -> bool {
        *self == SECURITY_MODE::Tee
    }
    #[doc = "Ree0 mode"]
    #[inline(always)]
    pub fn is_ree0(&self) -> bool {
        *self == SECURITY_MODE::Ree0
    }
    #[doc = "Ree1 mode"]
    #[inline(always)]
    pub fn is_ree1(&self) -> bool {
        *self == SECURITY_MODE::Ree1
    }
    #[doc = "Ree2 mode"]
    #[inline(always)]
    pub fn is_ree2(&self) -> bool {
        *self == SECURITY_MODE::Ree2
    }
}
#[doc = "Field `MODE` writer - M0 security level mode: 2'd3: ree_mode2. 2'd2: ree_mode1. 2'd1: ree_mode0. 2'd0: tee_mode"]
pub type MODE_W<'a, REG> = crate::FieldWriter<'a, REG, 2, SECURITY_MODE, crate::Safe>;
impl<'a, REG> MODE_W<'a, REG>
where
    REG: crate::Writable + crate::RegisterSpec,
    REG::Ux: From<u8>,
{
    #[doc = "Tee mode"]
    #[inline(always)]
    pub fn tee(self) -> &'a mut crate::W<REG> {
        self.variant(SECURITY_MODE::Tee)
    }
    #[doc = "Ree0 mode"]
    #[inline(always)]
    pub fn ree0(self) -> &'a mut crate::W<REG> {
        self.variant(SECURITY_MODE::Ree0)
    }
    #[doc = "Ree1 mode"]
    #[inline(always)]
    pub fn ree1(self) -> &'a mut crate::W<REG> {
        self.variant(SECURITY_MODE::Ree1)
    }
    #[doc = "Ree2 mode"]
    #[inline(always)]
    pub fn ree2(self) -> &'a mut crate::W<REG> {
        self.variant(SECURITY_MODE::Ree2)
    }
}
impl R {
    #[doc = "Bits 0:1 - M0 security level mode: 2'd3: ree_mode2. 2'd2: ree_mode1. 2'd1: ree_mode0. 2'd0: tee_mode"]
    #[inline(always)]
    pub fn mode(&self) -> MODE_R {
        MODE_R::new((self.bits & 3) as u8)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("M_MODE_CTRL")
            .field("mode", &self.mode())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:1 - M0 security level mode: 2'd3: ree_mode2. 2'd2: ree_mode1. 2'd1: ree_mode0. 2'd0: tee_mode"]
    #[inline(always)]
    pub fn mode(&mut self) -> MODE_W<'_, M_MODE_CTRL_SPEC> {
        MODE_W::new(self, 0)
    }
}
#[doc = "Tee mode control register\n\nYou can [`read`](crate::Reg::read) this register and get [`m_mode_ctrl::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`m_mode_ctrl::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct M_MODE_CTRL_SPEC;
impl crate::RegisterSpec for M_MODE_CTRL_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`m_mode_ctrl::R`](R) reader structure"]
impl crate::Readable for M_MODE_CTRL_SPEC {}
#[doc = "`write(|w| ..)` method takes [`m_mode_ctrl::W`](W) writer structure"]
impl crate::Writable for M_MODE_CTRL_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets M%s_MODE_CTRL to value 0x03"]
impl crate::Resettable for M_MODE_CTRL_SPEC {
    const RESET_VALUE: u32 = 0x03;
}
