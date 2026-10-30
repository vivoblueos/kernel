#[doc = "Register `WIN_CMD` reader"]
pub type R = crate::R<WIN_CMD_SPEC>;
#[doc = "Register `WIN_CMD` writer"]
pub type W = crate::W<WIN_CMD_SPEC>;
#[doc = "Field `SLCHOST_WIN_CMD` reader - *******Description***********"]
pub type SLCHOST_WIN_CMD_R = crate::FieldReader<u16>;
#[doc = "Field `SLCHOST_WIN_CMD` writer - *******Description***********"]
pub type SLCHOST_WIN_CMD_W<'a, REG> = crate::FieldWriter<'a, REG, 16, u16>;
impl R {
    #[doc = "Bits 0:15 - *******Description***********"]
    #[inline(always)]
    pub fn slchost_win_cmd(&self) -> SLCHOST_WIN_CMD_R {
        SLCHOST_WIN_CMD_R::new((self.bits & 0xffff) as u16)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("WIN_CMD")
            .field("slchost_win_cmd", &self.slchost_win_cmd())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:15 - *******Description***********"]
    #[inline(always)]
    pub fn slchost_win_cmd(&mut self) -> SLCHOST_WIN_CMD_W<'_, WIN_CMD_SPEC> {
        SLCHOST_WIN_CMD_W::new(self, 0)
    }
}
#[doc = "*******Description***********\n\nYou can [`read`](crate::Reg::read) this register and get [`win_cmd::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`win_cmd::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct WIN_CMD_SPEC;
impl crate::RegisterSpec for WIN_CMD_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`win_cmd::R`](R) reader structure"]
impl crate::Readable for WIN_CMD_SPEC {}
#[doc = "`write(|w| ..)` method takes [`win_cmd::W`](W) writer structure"]
impl crate::Writable for WIN_CMD_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets WIN_CMD to value 0"]
impl crate::Resettable for WIN_CMD_SPEC {}
