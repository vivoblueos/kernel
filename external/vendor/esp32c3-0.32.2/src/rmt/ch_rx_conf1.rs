#[doc = "Register `CH%s_RX_CONF1` reader"]
pub type R = crate::R<CH_RX_CONF1_SPEC>;
#[doc = "Register `CH%s_RX_CONF1` writer"]
pub type W = crate::W<CH_RX_CONF1_SPEC>;
#[doc = "Field `RX_EN` reader - reg_rx_en_ch2."]
pub type RX_EN_R = crate::BitReader;
#[doc = "Field `RX_EN` writer - reg_rx_en_ch2."]
pub type RX_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `MEM_WR_RST` writer - reg_mem_wr_rst_ch2."]
pub type MEM_WR_RST_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `APB_MEM_RST` writer - reg_apb_mem_rst_ch2."]
pub type APB_MEM_RST_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `MEM_OWNER` reader - reg_mem_owner_ch2."]
pub type MEM_OWNER_R = crate::BitReader;
#[doc = "Field `MEM_OWNER` writer - reg_mem_owner_ch2."]
pub type MEM_OWNER_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `RX_FILTER_EN` reader - reg_rx_filter_en_ch2."]
pub type RX_FILTER_EN_R = crate::BitReader;
#[doc = "Field `RX_FILTER_EN` writer - reg_rx_filter_en_ch2."]
pub type RX_FILTER_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `RX_FILTER_THRES` reader - reg_rx_filter_thres_ch2."]
pub type RX_FILTER_THRES_R = crate::FieldReader;
#[doc = "Field `RX_FILTER_THRES` writer - reg_rx_filter_thres_ch2."]
pub type RX_FILTER_THRES_W<'a, REG> = crate::FieldWriter<'a, REG, 8>;
#[doc = "Field `MEM_RX_WRAP_EN` reader - reg_mem_rx_wrap_en_ch2."]
pub type MEM_RX_WRAP_EN_R = crate::BitReader;
#[doc = "Field `MEM_RX_WRAP_EN` writer - reg_mem_rx_wrap_en_ch2."]
pub type MEM_RX_WRAP_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `AFIFO_RST` writer - reg_afifo_rst_ch2."]
pub type AFIFO_RST_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `CONF_UPDATE` writer - reg_conf_update_ch2."]
pub type CONF_UPDATE_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 0 - reg_rx_en_ch2."]
    #[inline(always)]
    pub fn rx_en(&self) -> RX_EN_R {
        RX_EN_R::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 3 - reg_mem_owner_ch2."]
    #[inline(always)]
    pub fn mem_owner(&self) -> MEM_OWNER_R {
        MEM_OWNER_R::new(((self.bits >> 3) & 1) != 0)
    }
    #[doc = "Bit 4 - reg_rx_filter_en_ch2."]
    #[inline(always)]
    pub fn rx_filter_en(&self) -> RX_FILTER_EN_R {
        RX_FILTER_EN_R::new(((self.bits >> 4) & 1) != 0)
    }
    #[doc = "Bits 5:12 - reg_rx_filter_thres_ch2."]
    #[inline(always)]
    pub fn rx_filter_thres(&self) -> RX_FILTER_THRES_R {
        RX_FILTER_THRES_R::new(((self.bits >> 5) & 0xff) as u8)
    }
    #[doc = "Bit 13 - reg_mem_rx_wrap_en_ch2."]
    #[inline(always)]
    pub fn mem_rx_wrap_en(&self) -> MEM_RX_WRAP_EN_R {
        MEM_RX_WRAP_EN_R::new(((self.bits >> 13) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("CH_RX_CONF1")
            .field("rx_en", &self.rx_en())
            .field("mem_owner", &self.mem_owner())
            .field("rx_filter_en", &self.rx_filter_en())
            .field("rx_filter_thres", &self.rx_filter_thres())
            .field("mem_rx_wrap_en", &self.mem_rx_wrap_en())
            .finish()
    }
}
impl W {
    #[doc = "Bit 0 - reg_rx_en_ch2."]
    #[inline(always)]
    pub fn rx_en(&mut self) -> RX_EN_W<'_, CH_RX_CONF1_SPEC> {
        RX_EN_W::new(self, 0)
    }
    #[doc = "Bit 1 - reg_mem_wr_rst_ch2."]
    #[inline(always)]
    pub fn mem_wr_rst(&mut self) -> MEM_WR_RST_W<'_, CH_RX_CONF1_SPEC> {
        MEM_WR_RST_W::new(self, 1)
    }
    #[doc = "Bit 2 - reg_apb_mem_rst_ch2."]
    #[inline(always)]
    pub fn apb_mem_rst(&mut self) -> APB_MEM_RST_W<'_, CH_RX_CONF1_SPEC> {
        APB_MEM_RST_W::new(self, 2)
    }
    #[doc = "Bit 3 - reg_mem_owner_ch2."]
    #[inline(always)]
    pub fn mem_owner(&mut self) -> MEM_OWNER_W<'_, CH_RX_CONF1_SPEC> {
        MEM_OWNER_W::new(self, 3)
    }
    #[doc = "Bit 4 - reg_rx_filter_en_ch2."]
    #[inline(always)]
    pub fn rx_filter_en(&mut self) -> RX_FILTER_EN_W<'_, CH_RX_CONF1_SPEC> {
        RX_FILTER_EN_W::new(self, 4)
    }
    #[doc = "Bits 5:12 - reg_rx_filter_thres_ch2."]
    #[inline(always)]
    pub fn rx_filter_thres(&mut self) -> RX_FILTER_THRES_W<'_, CH_RX_CONF1_SPEC> {
        RX_FILTER_THRES_W::new(self, 5)
    }
    #[doc = "Bit 13 - reg_mem_rx_wrap_en_ch2."]
    #[inline(always)]
    pub fn mem_rx_wrap_en(&mut self) -> MEM_RX_WRAP_EN_W<'_, CH_RX_CONF1_SPEC> {
        MEM_RX_WRAP_EN_W::new(self, 13)
    }
    #[doc = "Bit 14 - reg_afifo_rst_ch2."]
    #[inline(always)]
    pub fn afifo_rst(&mut self) -> AFIFO_RST_W<'_, CH_RX_CONF1_SPEC> {
        AFIFO_RST_W::new(self, 14)
    }
    #[doc = "Bit 15 - reg_conf_update_ch2."]
    #[inline(always)]
    pub fn conf_update(&mut self) -> CONF_UPDATE_W<'_, CH_RX_CONF1_SPEC> {
        CONF_UPDATE_W::new(self, 15)
    }
}
#[doc = "RMT_CH2CONF1_REG.\n\nYou can [`read`](crate::Reg::read) this register and get [`ch_rx_conf1::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`ch_rx_conf1::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct CH_RX_CONF1_SPEC;
impl crate::RegisterSpec for CH_RX_CONF1_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`ch_rx_conf1::R`](R) reader structure"]
impl crate::Readable for CH_RX_CONF1_SPEC {}
#[doc = "`write(|w| ..)` method takes [`ch_rx_conf1::W`](W) writer structure"]
impl crate::Writable for CH_RX_CONF1_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets CH%s_RX_CONF1 to value 0x01e8"]
impl crate::Resettable for CH_RX_CONF1_SPEC {
    const RESET_VALUE: u32 = 0x01e8;
}
