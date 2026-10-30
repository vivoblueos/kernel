#[doc = "Register `DIEP0TFSTAT` reader"]
pub type R = crate::R<Diep0tfstatSpec>;
#[doc = "Field `IEPTFS` reader - IN endpoint TxFIFO space remaining"]
pub type IeptfsR = crate::FieldReader<u16>;
impl R {
    #[doc = "Bits 0:15 - IN endpoint TxFIFO space remaining"]
    #[inline(always)]
    pub fn ieptfs(&self) -> IeptfsR {
        IeptfsR::new((self.bits & 0xffff) as u16)
    }
}
#[doc = "device IN endpoint 0 transmit FIFO status register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`diep0tfstat::R`](R).  See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct Diep0tfstatSpec;
impl crate::RegisterSpec for Diep0tfstatSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`diep0tfstat::R`](R) reader structure"]
impl crate::Readable for Diep0tfstatSpec {}
#[doc = "`reset()` method sets DIEP0TFSTAT to value 0x0200"]
impl crate::Resettable for Diep0tfstatSpec {
    const RESET_VALUE: u32 = 0x0200;
}
