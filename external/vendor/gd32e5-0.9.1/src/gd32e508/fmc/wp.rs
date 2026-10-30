#[doc = "Register `WP` reader"]
pub type R = crate::R<WpSpec>;
#[doc = "Field `WP` reader - Store WP\\[31:0\\]
of option bytes block after system reset"]
pub type WpR = crate::FieldReader<u32>;
impl R {
    #[doc = "Bits 0:31 - Store WP\\[31:0\\]
of option bytes block after system reset"]
    #[inline(always)]
    pub fn wp(&self) -> WpR {
        WpR::new(self.bits)
    }
}
#[doc = "Erase/Program Protection register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`wp::R`](R).  See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct WpSpec;
impl crate::RegisterSpec for WpSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`wp::R`](R) reader structure"]
impl crate::Readable for WpSpec {}
#[doc = "`reset()` method sets WP to value 0xffff_ffff"]
impl crate::Resettable for WpSpec {
    const RESET_VALUE: u32 = 0xffff_ffff;
}
