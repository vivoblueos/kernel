#[doc = "Register `STATE_W1` reader"]
pub type R = crate::R<STATE_W1_SPEC>;
#[doc = "Field `SLCHOST_STATE4` reader - *******Description***********"]
pub type SLCHOST_STATE4_R = crate::FieldReader;
#[doc = "Field `SLCHOST_STATE5` reader - *******Description***********"]
pub type SLCHOST_STATE5_R = crate::FieldReader;
#[doc = "Field `SLCHOST_STATE6` reader - *******Description***********"]
pub type SLCHOST_STATE6_R = crate::FieldReader;
#[doc = "Field `SLCHOST_STATE7` reader - *******Description***********"]
pub type SLCHOST_STATE7_R = crate::FieldReader;
impl R {
    #[doc = "Bits 0:7 - *******Description***********"]
    #[inline(always)]
    pub fn slchost_state4(&self) -> SLCHOST_STATE4_R {
        SLCHOST_STATE4_R::new((self.bits & 0xff) as u8)
    }
    #[doc = "Bits 8:15 - *******Description***********"]
    #[inline(always)]
    pub fn slchost_state5(&self) -> SLCHOST_STATE5_R {
        SLCHOST_STATE5_R::new(((self.bits >> 8) & 0xff) as u8)
    }
    #[doc = "Bits 16:23 - *******Description***********"]
    #[inline(always)]
    pub fn slchost_state6(&self) -> SLCHOST_STATE6_R {
        SLCHOST_STATE6_R::new(((self.bits >> 16) & 0xff) as u8)
    }
    #[doc = "Bits 24:31 - *******Description***********"]
    #[inline(always)]
    pub fn slchost_state7(&self) -> SLCHOST_STATE7_R {
        SLCHOST_STATE7_R::new(((self.bits >> 24) & 0xff) as u8)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("STATE_W1")
            .field("slchost_state4", &self.slchost_state4())
            .field("slchost_state5", &self.slchost_state5())
            .field("slchost_state6", &self.slchost_state6())
            .field("slchost_state7", &self.slchost_state7())
            .finish()
    }
}
#[doc = "*******Description***********\n\nYou can [`read`](crate::Reg::read) this register and get [`state_w1::R`](R). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct STATE_W1_SPEC;
impl crate::RegisterSpec for STATE_W1_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`state_w1::R`](R) reader structure"]
impl crate::Readable for STATE_W1_SPEC {}
#[doc = "`reset()` method sets STATE_W1 to value 0"]
impl crate::Resettable for STATE_W1_SPEC {}
