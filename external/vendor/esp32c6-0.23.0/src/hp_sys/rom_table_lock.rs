#[doc = "Register `ROM_TABLE_LOCK` reader"]
pub type R = crate::R<ROM_TABLE_LOCK_SPEC>;
#[doc = "Register `ROM_TABLE_LOCK` writer"]
pub type W = crate::W<ROM_TABLE_LOCK_SPEC>;
#[doc = "Field `ROM_TABLE_LOCK` reader - XXXX"]
pub type ROM_TABLE_LOCK_R = crate::BitReader;
#[doc = "Field `ROM_TABLE_LOCK` writer - XXXX"]
pub type ROM_TABLE_LOCK_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 0 - XXXX"]
    #[inline(always)]
    pub fn rom_table_lock(&self) -> ROM_TABLE_LOCK_R {
        ROM_TABLE_LOCK_R::new((self.bits & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("ROM_TABLE_LOCK")
            .field("rom_table_lock", &self.rom_table_lock())
            .finish()
    }
}
impl W {
    #[doc = "Bit 0 - XXXX"]
    #[inline(always)]
    pub fn rom_table_lock(&mut self) -> ROM_TABLE_LOCK_W<'_, ROM_TABLE_LOCK_SPEC> {
        ROM_TABLE_LOCK_W::new(self, 0)
    }
}
#[doc = "Rom-Table lock register\n\nYou can [`read`](crate::Reg::read) this register and get [`rom_table_lock::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`rom_table_lock::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct ROM_TABLE_LOCK_SPEC;
impl crate::RegisterSpec for ROM_TABLE_LOCK_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`rom_table_lock::R`](R) reader structure"]
impl crate::Readable for ROM_TABLE_LOCK_SPEC {}
#[doc = "`write(|w| ..)` method takes [`rom_table_lock::W`](W) writer structure"]
impl crate::Writable for ROM_TABLE_LOCK_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets ROM_TABLE_LOCK to value 0"]
impl crate::Resettable for ROM_TABLE_LOCK_SPEC {}
