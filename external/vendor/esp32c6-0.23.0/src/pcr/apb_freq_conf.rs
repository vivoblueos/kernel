#[doc = "Register `APB_FREQ_CONF` reader"]
pub type R = crate::R<APB_FREQ_CONF_SPEC>;
#[doc = "Register `APB_FREQ_CONF` writer"]
pub type W = crate::W<APB_FREQ_CONF_SPEC>;
#[doc = "Field `APB_DECREASE_DIV_NUM` reader - If this field's value is grater than PCR_APB_DIV_NUM, the clk_apb will be automatically down to clk_apb_decrease only when no access is on apb-bus, and will recover to the previous frequency when a new access appears on apb-bus. Set as one within (0,1,3) to set clk_apb_decrease as div1/div2/div4(default) of clk_ahb. Note that enable this function will reduce performance. Users can set this field as zero to disable the auto-decrease-apb-freq function. By default, this function is disable."]
pub type APB_DECREASE_DIV_NUM_R = crate::FieldReader;
#[doc = "Field `APB_DECREASE_DIV_NUM` writer - If this field's value is grater than PCR_APB_DIV_NUM, the clk_apb will be automatically down to clk_apb_decrease only when no access is on apb-bus, and will recover to the previous frequency when a new access appears on apb-bus. Set as one within (0,1,3) to set clk_apb_decrease as div1/div2/div4(default) of clk_ahb. Note that enable this function will reduce performance. Users can set this field as zero to disable the auto-decrease-apb-freq function. By default, this function is disable."]
pub type APB_DECREASE_DIV_NUM_W<'a, REG> = crate::FieldWriter<'a, REG, 8>;
#[doc = "Field `APB_DIV_NUM` reader - Set as one within (0,1,3) to generate clk_apb drived by clk_ahb. The clk_apb is div1(default)/div2/div4 of clk_ahb."]
pub type APB_DIV_NUM_R = crate::FieldReader;
#[doc = "Field `APB_DIV_NUM` writer - Set as one within (0,1,3) to generate clk_apb drived by clk_ahb. The clk_apb is div1(default)/div2/div4 of clk_ahb."]
pub type APB_DIV_NUM_W<'a, REG> = crate::FieldWriter<'a, REG, 8>;
impl R {
    #[doc = "Bits 0:7 - If this field's value is grater than PCR_APB_DIV_NUM, the clk_apb will be automatically down to clk_apb_decrease only when no access is on apb-bus, and will recover to the previous frequency when a new access appears on apb-bus. Set as one within (0,1,3) to set clk_apb_decrease as div1/div2/div4(default) of clk_ahb. Note that enable this function will reduce performance. Users can set this field as zero to disable the auto-decrease-apb-freq function. By default, this function is disable."]
    #[inline(always)]
    pub fn apb_decrease_div_num(&self) -> APB_DECREASE_DIV_NUM_R {
        APB_DECREASE_DIV_NUM_R::new((self.bits & 0xff) as u8)
    }
    #[doc = "Bits 8:15 - Set as one within (0,1,3) to generate clk_apb drived by clk_ahb. The clk_apb is div1(default)/div2/div4 of clk_ahb."]
    #[inline(always)]
    pub fn apb_div_num(&self) -> APB_DIV_NUM_R {
        APB_DIV_NUM_R::new(((self.bits >> 8) & 0xff) as u8)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("APB_FREQ_CONF")
            .field("apb_decrease_div_num", &self.apb_decrease_div_num())
            .field("apb_div_num", &self.apb_div_num())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:7 - If this field's value is grater than PCR_APB_DIV_NUM, the clk_apb will be automatically down to clk_apb_decrease only when no access is on apb-bus, and will recover to the previous frequency when a new access appears on apb-bus. Set as one within (0,1,3) to set clk_apb_decrease as div1/div2/div4(default) of clk_ahb. Note that enable this function will reduce performance. Users can set this field as zero to disable the auto-decrease-apb-freq function. By default, this function is disable."]
    #[inline(always)]
    pub fn apb_decrease_div_num(&mut self) -> APB_DECREASE_DIV_NUM_W<'_, APB_FREQ_CONF_SPEC> {
        APB_DECREASE_DIV_NUM_W::new(self, 0)
    }
    #[doc = "Bits 8:15 - Set as one within (0,1,3) to generate clk_apb drived by clk_ahb. The clk_apb is div1(default)/div2/div4 of clk_ahb."]
    #[inline(always)]
    pub fn apb_div_num(&mut self) -> APB_DIV_NUM_W<'_, APB_FREQ_CONF_SPEC> {
        APB_DIV_NUM_W::new(self, 8)
    }
}
#[doc = "APB_FREQ configuration register\n\nYou can [`read`](crate::Reg::read) this register and get [`apb_freq_conf::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`apb_freq_conf::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct APB_FREQ_CONF_SPEC;
impl crate::RegisterSpec for APB_FREQ_CONF_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`apb_freq_conf::R`](R) reader structure"]
impl crate::Readable for APB_FREQ_CONF_SPEC {}
#[doc = "`write(|w| ..)` method takes [`apb_freq_conf::W`](W) writer structure"]
impl crate::Writable for APB_FREQ_CONF_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets APB_FREQ_CONF to value 0"]
impl crate::Resettable for APB_FREQ_CONF_SPEC {}
