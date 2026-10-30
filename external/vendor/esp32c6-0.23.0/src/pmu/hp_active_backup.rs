#[doc = "Register `HP_ACTIVE_BACKUP` reader"]
pub type R = crate::R<HP_ACTIVE_BACKUP_SPEC>;
#[doc = "Register `HP_ACTIVE_BACKUP` writer"]
pub type W = crate::W<HP_ACTIVE_BACKUP_SPEC>;
#[doc = "Field `HP_SLEEP2ACTIVE_BACKUP_MODEM_CLK_CODE` reader - need_des"]
pub type HP_SLEEP2ACTIVE_BACKUP_MODEM_CLK_CODE_R = crate::FieldReader;
#[doc = "Field `HP_SLEEP2ACTIVE_BACKUP_MODEM_CLK_CODE` writer - need_des"]
pub type HP_SLEEP2ACTIVE_BACKUP_MODEM_CLK_CODE_W<'a, REG> = crate::FieldWriter<'a, REG, 2>;
#[doc = "Field `HP_MODEM2ACTIVE_BACKUP_MODEM_CLK_CODE` reader - need_des"]
pub type HP_MODEM2ACTIVE_BACKUP_MODEM_CLK_CODE_R = crate::FieldReader;
#[doc = "Field `HP_MODEM2ACTIVE_BACKUP_MODEM_CLK_CODE` writer - need_des"]
pub type HP_MODEM2ACTIVE_BACKUP_MODEM_CLK_CODE_W<'a, REG> = crate::FieldWriter<'a, REG, 2>;
#[doc = "Field `HP_ACTIVE_RETENTION_MODE` reader - need_des"]
pub type HP_ACTIVE_RETENTION_MODE_R = crate::BitReader;
#[doc = "Field `HP_ACTIVE_RETENTION_MODE` writer - need_des"]
pub type HP_ACTIVE_RETENTION_MODE_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `HP_SLEEP2ACTIVE_RETENTION_EN` reader - need_des"]
pub type HP_SLEEP2ACTIVE_RETENTION_EN_R = crate::BitReader;
#[doc = "Field `HP_SLEEP2ACTIVE_RETENTION_EN` writer - need_des"]
pub type HP_SLEEP2ACTIVE_RETENTION_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `HP_MODEM2ACTIVE_RETENTION_EN` reader - need_des"]
pub type HP_MODEM2ACTIVE_RETENTION_EN_R = crate::BitReader;
#[doc = "Field `HP_MODEM2ACTIVE_RETENTION_EN` writer - need_des"]
pub type HP_MODEM2ACTIVE_RETENTION_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `HP_SLEEP2ACTIVE_BACKUP_CLK_SEL` reader - need_des"]
pub type HP_SLEEP2ACTIVE_BACKUP_CLK_SEL_R = crate::FieldReader;
#[doc = "Field `HP_SLEEP2ACTIVE_BACKUP_CLK_SEL` writer - need_des"]
pub type HP_SLEEP2ACTIVE_BACKUP_CLK_SEL_W<'a, REG> = crate::FieldWriter<'a, REG, 2>;
#[doc = "Field `HP_MODEM2ACTIVE_BACKUP_CLK_SEL` reader - need_des"]
pub type HP_MODEM2ACTIVE_BACKUP_CLK_SEL_R = crate::FieldReader;
#[doc = "Field `HP_MODEM2ACTIVE_BACKUP_CLK_SEL` writer - need_des"]
pub type HP_MODEM2ACTIVE_BACKUP_CLK_SEL_W<'a, REG> = crate::FieldWriter<'a, REG, 2>;
#[doc = "Field `HP_SLEEP2ACTIVE_BACKUP_MODE` reader - need_des"]
pub type HP_SLEEP2ACTIVE_BACKUP_MODE_R = crate::FieldReader;
#[doc = "Field `HP_SLEEP2ACTIVE_BACKUP_MODE` writer - need_des"]
pub type HP_SLEEP2ACTIVE_BACKUP_MODE_W<'a, REG> = crate::FieldWriter<'a, REG, 3>;
#[doc = "Field `HP_MODEM2ACTIVE_BACKUP_MODE` reader - need_des"]
pub type HP_MODEM2ACTIVE_BACKUP_MODE_R = crate::FieldReader;
#[doc = "Field `HP_MODEM2ACTIVE_BACKUP_MODE` writer - need_des"]
pub type HP_MODEM2ACTIVE_BACKUP_MODE_W<'a, REG> = crate::FieldWriter<'a, REG, 3>;
#[doc = "Field `HP_SLEEP2ACTIVE_BACKUP_EN` reader - need_des"]
pub type HP_SLEEP2ACTIVE_BACKUP_EN_R = crate::BitReader;
#[doc = "Field `HP_SLEEP2ACTIVE_BACKUP_EN` writer - need_des"]
pub type HP_SLEEP2ACTIVE_BACKUP_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `HP_MODEM2ACTIVE_BACKUP_EN` reader - need_des"]
pub type HP_MODEM2ACTIVE_BACKUP_EN_R = crate::BitReader;
#[doc = "Field `HP_MODEM2ACTIVE_BACKUP_EN` writer - need_des"]
pub type HP_MODEM2ACTIVE_BACKUP_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bits 4:5 - need_des"]
    #[inline(always)]
    pub fn hp_sleep2active_backup_modem_clk_code(&self) -> HP_SLEEP2ACTIVE_BACKUP_MODEM_CLK_CODE_R {
        HP_SLEEP2ACTIVE_BACKUP_MODEM_CLK_CODE_R::new(((self.bits >> 4) & 3) as u8)
    }
    #[doc = "Bits 6:7 - need_des"]
    #[inline(always)]
    pub fn hp_modem2active_backup_modem_clk_code(&self) -> HP_MODEM2ACTIVE_BACKUP_MODEM_CLK_CODE_R {
        HP_MODEM2ACTIVE_BACKUP_MODEM_CLK_CODE_R::new(((self.bits >> 6) & 3) as u8)
    }
    #[doc = "Bit 10 - need_des"]
    #[inline(always)]
    pub fn hp_active_retention_mode(&self) -> HP_ACTIVE_RETENTION_MODE_R {
        HP_ACTIVE_RETENTION_MODE_R::new(((self.bits >> 10) & 1) != 0)
    }
    #[doc = "Bit 11 - need_des"]
    #[inline(always)]
    pub fn hp_sleep2active_retention_en(&self) -> HP_SLEEP2ACTIVE_RETENTION_EN_R {
        HP_SLEEP2ACTIVE_RETENTION_EN_R::new(((self.bits >> 11) & 1) != 0)
    }
    #[doc = "Bit 12 - need_des"]
    #[inline(always)]
    pub fn hp_modem2active_retention_en(&self) -> HP_MODEM2ACTIVE_RETENTION_EN_R {
        HP_MODEM2ACTIVE_RETENTION_EN_R::new(((self.bits >> 12) & 1) != 0)
    }
    #[doc = "Bits 14:15 - need_des"]
    #[inline(always)]
    pub fn hp_sleep2active_backup_clk_sel(&self) -> HP_SLEEP2ACTIVE_BACKUP_CLK_SEL_R {
        HP_SLEEP2ACTIVE_BACKUP_CLK_SEL_R::new(((self.bits >> 14) & 3) as u8)
    }
    #[doc = "Bits 16:17 - need_des"]
    #[inline(always)]
    pub fn hp_modem2active_backup_clk_sel(&self) -> HP_MODEM2ACTIVE_BACKUP_CLK_SEL_R {
        HP_MODEM2ACTIVE_BACKUP_CLK_SEL_R::new(((self.bits >> 16) & 3) as u8)
    }
    #[doc = "Bits 20:22 - need_des"]
    #[inline(always)]
    pub fn hp_sleep2active_backup_mode(&self) -> HP_SLEEP2ACTIVE_BACKUP_MODE_R {
        HP_SLEEP2ACTIVE_BACKUP_MODE_R::new(((self.bits >> 20) & 7) as u8)
    }
    #[doc = "Bits 23:25 - need_des"]
    #[inline(always)]
    pub fn hp_modem2active_backup_mode(&self) -> HP_MODEM2ACTIVE_BACKUP_MODE_R {
        HP_MODEM2ACTIVE_BACKUP_MODE_R::new(((self.bits >> 23) & 7) as u8)
    }
    #[doc = "Bit 29 - need_des"]
    #[inline(always)]
    pub fn hp_sleep2active_backup_en(&self) -> HP_SLEEP2ACTIVE_BACKUP_EN_R {
        HP_SLEEP2ACTIVE_BACKUP_EN_R::new(((self.bits >> 29) & 1) != 0)
    }
    #[doc = "Bit 30 - need_des"]
    #[inline(always)]
    pub fn hp_modem2active_backup_en(&self) -> HP_MODEM2ACTIVE_BACKUP_EN_R {
        HP_MODEM2ACTIVE_BACKUP_EN_R::new(((self.bits >> 30) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("HP_ACTIVE_BACKUP")
            .field(
                "hp_sleep2active_backup_modem_clk_code",
                &self.hp_sleep2active_backup_modem_clk_code(),
            )
            .field(
                "hp_modem2active_backup_modem_clk_code",
                &self.hp_modem2active_backup_modem_clk_code(),
            )
            .field("hp_active_retention_mode", &self.hp_active_retention_mode())
            .field(
                "hp_sleep2active_retention_en",
                &self.hp_sleep2active_retention_en(),
            )
            .field(
                "hp_modem2active_retention_en",
                &self.hp_modem2active_retention_en(),
            )
            .field(
                "hp_sleep2active_backup_clk_sel",
                &self.hp_sleep2active_backup_clk_sel(),
            )
            .field(
                "hp_modem2active_backup_clk_sel",
                &self.hp_modem2active_backup_clk_sel(),
            )
            .field(
                "hp_sleep2active_backup_mode",
                &self.hp_sleep2active_backup_mode(),
            )
            .field(
                "hp_modem2active_backup_mode",
                &self.hp_modem2active_backup_mode(),
            )
            .field(
                "hp_sleep2active_backup_en",
                &self.hp_sleep2active_backup_en(),
            )
            .field(
                "hp_modem2active_backup_en",
                &self.hp_modem2active_backup_en(),
            )
            .finish()
    }
}
impl W {
    #[doc = "Bits 4:5 - need_des"]
    #[inline(always)]
    pub fn hp_sleep2active_backup_modem_clk_code(
        &mut self,
    ) -> HP_SLEEP2ACTIVE_BACKUP_MODEM_CLK_CODE_W<'_, HP_ACTIVE_BACKUP_SPEC> {
        HP_SLEEP2ACTIVE_BACKUP_MODEM_CLK_CODE_W::new(self, 4)
    }
    #[doc = "Bits 6:7 - need_des"]
    #[inline(always)]
    pub fn hp_modem2active_backup_modem_clk_code(
        &mut self,
    ) -> HP_MODEM2ACTIVE_BACKUP_MODEM_CLK_CODE_W<'_, HP_ACTIVE_BACKUP_SPEC> {
        HP_MODEM2ACTIVE_BACKUP_MODEM_CLK_CODE_W::new(self, 6)
    }
    #[doc = "Bit 10 - need_des"]
    #[inline(always)]
    pub fn hp_active_retention_mode(
        &mut self,
    ) -> HP_ACTIVE_RETENTION_MODE_W<'_, HP_ACTIVE_BACKUP_SPEC> {
        HP_ACTIVE_RETENTION_MODE_W::new(self, 10)
    }
    #[doc = "Bit 11 - need_des"]
    #[inline(always)]
    pub fn hp_sleep2active_retention_en(
        &mut self,
    ) -> HP_SLEEP2ACTIVE_RETENTION_EN_W<'_, HP_ACTIVE_BACKUP_SPEC> {
        HP_SLEEP2ACTIVE_RETENTION_EN_W::new(self, 11)
    }
    #[doc = "Bit 12 - need_des"]
    #[inline(always)]
    pub fn hp_modem2active_retention_en(
        &mut self,
    ) -> HP_MODEM2ACTIVE_RETENTION_EN_W<'_, HP_ACTIVE_BACKUP_SPEC> {
        HP_MODEM2ACTIVE_RETENTION_EN_W::new(self, 12)
    }
    #[doc = "Bits 14:15 - need_des"]
    #[inline(always)]
    pub fn hp_sleep2active_backup_clk_sel(
        &mut self,
    ) -> HP_SLEEP2ACTIVE_BACKUP_CLK_SEL_W<'_, HP_ACTIVE_BACKUP_SPEC> {
        HP_SLEEP2ACTIVE_BACKUP_CLK_SEL_W::new(self, 14)
    }
    #[doc = "Bits 16:17 - need_des"]
    #[inline(always)]
    pub fn hp_modem2active_backup_clk_sel(
        &mut self,
    ) -> HP_MODEM2ACTIVE_BACKUP_CLK_SEL_W<'_, HP_ACTIVE_BACKUP_SPEC> {
        HP_MODEM2ACTIVE_BACKUP_CLK_SEL_W::new(self, 16)
    }
    #[doc = "Bits 20:22 - need_des"]
    #[inline(always)]
    pub fn hp_sleep2active_backup_mode(
        &mut self,
    ) -> HP_SLEEP2ACTIVE_BACKUP_MODE_W<'_, HP_ACTIVE_BACKUP_SPEC> {
        HP_SLEEP2ACTIVE_BACKUP_MODE_W::new(self, 20)
    }
    #[doc = "Bits 23:25 - need_des"]
    #[inline(always)]
    pub fn hp_modem2active_backup_mode(
        &mut self,
    ) -> HP_MODEM2ACTIVE_BACKUP_MODE_W<'_, HP_ACTIVE_BACKUP_SPEC> {
        HP_MODEM2ACTIVE_BACKUP_MODE_W::new(self, 23)
    }
    #[doc = "Bit 29 - need_des"]
    #[inline(always)]
    pub fn hp_sleep2active_backup_en(
        &mut self,
    ) -> HP_SLEEP2ACTIVE_BACKUP_EN_W<'_, HP_ACTIVE_BACKUP_SPEC> {
        HP_SLEEP2ACTIVE_BACKUP_EN_W::new(self, 29)
    }
    #[doc = "Bit 30 - need_des"]
    #[inline(always)]
    pub fn hp_modem2active_backup_en(
        &mut self,
    ) -> HP_MODEM2ACTIVE_BACKUP_EN_W<'_, HP_ACTIVE_BACKUP_SPEC> {
        HP_MODEM2ACTIVE_BACKUP_EN_W::new(self, 30)
    }
}
#[doc = "need_des\n\nYou can [`read`](crate::Reg::read) this register and get [`hp_active_backup::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`hp_active_backup::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct HP_ACTIVE_BACKUP_SPEC;
impl crate::RegisterSpec for HP_ACTIVE_BACKUP_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`hp_active_backup::R`](R) reader structure"]
impl crate::Readable for HP_ACTIVE_BACKUP_SPEC {}
#[doc = "`write(|w| ..)` method takes [`hp_active_backup::W`](W) writer structure"]
impl crate::Writable for HP_ACTIVE_BACKUP_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets HP_ACTIVE_BACKUP to value 0"]
impl crate::Resettable for HP_ACTIVE_BACKUP_SPEC {}
