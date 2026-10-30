#[doc = "Register `IFS_COUNTER` reader"]
pub type R = crate::R<IFS_COUNTER_SPEC>;
#[doc = "Register `IFS_COUNTER` writer"]
pub type W = crate::W<IFS_COUNTER_SPEC>;
#[doc = "Field `IFS_COUNTER` reader - "]
pub type IFS_COUNTER_R = crate::FieldReader<u16>;
#[doc = "Field `IFS_COUNTER` writer - "]
pub type IFS_COUNTER_W<'a, REG> = crate::FieldWriter<'a, REG, 10, u16>;
#[doc = "Field `EN` reader - "]
pub type EN_R = crate::BitReader;
#[doc = "Field `EN` writer - "]
pub type EN_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bits 0:9"]
    #[inline(always)]
    pub fn ifs_counter(&self) -> IFS_COUNTER_R {
        IFS_COUNTER_R::new((self.bits & 0x03ff) as u16)
    }
    #[doc = "Bit 16"]
    #[inline(always)]
    pub fn en(&self) -> EN_R {
        EN_R::new(((self.bits >> 16) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("IFS_COUNTER")
            .field("ifs_counter", &self.ifs_counter())
            .field("en", &self.en())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:9"]
    #[inline(always)]
    pub fn ifs_counter(&mut self) -> IFS_COUNTER_W<'_, IFS_COUNTER_SPEC> {
        IFS_COUNTER_W::new(self, 0)
    }
    #[doc = "Bit 16"]
    #[inline(always)]
    pub fn en(&mut self) -> EN_W<'_, IFS_COUNTER_SPEC> {
        EN_W::new(self, 16)
    }
}
#[doc = "\n\nYou can [`read`](crate::Reg::read) this register and get [`ifs_counter::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`ifs_counter::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct IFS_COUNTER_SPEC;
impl crate::RegisterSpec for IFS_COUNTER_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`ifs_counter::R`](R) reader structure"]
impl crate::Readable for IFS_COUNTER_SPEC {}
#[doc = "`write(|w| ..)` method takes [`ifs_counter::W`](W) writer structure"]
impl crate::Writable for IFS_COUNTER_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets IFS_COUNTER to value 0"]
impl crate::Resettable for IFS_COUNTER_SPEC {}
