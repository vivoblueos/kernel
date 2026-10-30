#[doc = "Register `DIEP5TFSTAT` reader"]
pub type R = crate::R<Diep5tfstatSpec>;
#[doc = "Field `IEPTFS` reader - IN endpoint TxFIFO space remaining"]
pub type IeptfsR = crate::FieldReader<u16>;
impl R {
    #[doc = "Bits 0:15 - IN endpoint TxFIFO space remaining"]
    #[inline(always)]
    pub fn ieptfs(&self) -> IeptfsR {
        IeptfsR::new((self.bits & 0xffff) as u16)
    }
}
#[doc = "device IN endpoint 5 transmit FIFO status register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`diep5tfstat::R`](R).  See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct Diep5tfstatSpec;
impl crate::RegisterSpec for Diep5tfstatSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`diep5tfstat::R`](R) reader structure"]
impl crate::Readable for Diep5tfstatSpec {}
#[doc = "`reset()` method sets DIEP5TFSTAT to value 0x0200"]
impl crate::Resettable for Diep5tfstatSpec {
    const RESET_VALUE: u32 = 0x0200;
}
