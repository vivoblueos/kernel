#[doc = "Register `DIEP3TFSTAT` reader"]
pub type R = crate::R<Diep3tfstatSpec>;
#[doc = "Field `IEPTFS` reader - IN endpoint TxFIFO space remaining"]
pub type IeptfsR = crate::FieldReader<u16>;
impl R {
    #[doc = "Bits 0:15 - IN endpoint TxFIFO space remaining"]
    #[inline(always)]
    pub fn ieptfs(&self) -> IeptfsR {
        IeptfsR::new((self.bits & 0xffff) as u16)
    }
}
#[doc = "device IN endpoint 3 transmit FIFO status register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`diep3tfstat::R`](R).  See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct Diep3tfstatSpec;
impl crate::RegisterSpec for Diep3tfstatSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`diep3tfstat::R`](R) reader structure"]
impl crate::Readable for Diep3tfstatSpec {}
#[doc = "`reset()` method sets DIEP3TFSTAT to value 0x0200"]
impl crate::Resettable for Diep3tfstatSpec {
    const RESET_VALUE: u32 = 0x0200;
}
