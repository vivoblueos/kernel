#[doc = "Register `DIEP1TFSTAT` reader"]
pub type R = crate::R<Diep1tfstatSpec>;
#[doc = "Field `IEPTFS` reader - IN endpoint TxFIFO space remaining"]
pub type IeptfsR = crate::FieldReader<u16>;
impl R {
    #[doc = "Bits 0:15 - IN endpoint TxFIFO space remaining"]
    #[inline(always)]
    pub fn ieptfs(&self) -> IeptfsR {
        IeptfsR::new((self.bits & 0xffff) as u16)
    }
}
#[doc = "device IN endpoint 1 transmit FIFO status register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`diep1tfstat::R`](R).  See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct Diep1tfstatSpec;
impl crate::RegisterSpec for Diep1tfstatSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`diep1tfstat::R`](R) reader structure"]
impl crate::Readable for Diep1tfstatSpec {}
#[doc = "`reset()` method sets DIEP1TFSTAT to value 0x0200"]
impl crate::Resettable for Diep1tfstatSpec {
    const RESET_VALUE: u32 = 0x0200;
}
