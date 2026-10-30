#[doc = "Register `IOFF3` reader"]
pub type R = crate::R<Ioff3Spec>;
#[doc = "Register `IOFF3` writer"]
pub type W = crate::W<Ioff3Spec>;
#[doc = "Field `IOFF` reader - Data offset for inserted channel 3"]
pub type IoffR = crate::FieldReader<u16>;
#[doc = "Field `IOFF` writer - Data offset for inserted channel 3"]
pub type IoffW<'a, REG> = crate::FieldWriter<'a, REG, 12, u16>;
impl R {
    #[doc = "Bits 0:11 - Data offset for inserted channel 3"]
    #[inline(always)]
    pub fn ioff(&self) -> IoffR {
        IoffR::new((self.bits & 0x0fff) as u16)
    }
}
impl W {
    #[doc = "Bits 0:11 - Data offset for inserted channel 3"]
    #[inline(always)]
    #[must_use]
    pub fn ioff(&mut self) -> IoffW<Ioff3Spec> {
        IoffW::new(self, 0)
    }
}
#[doc = "Inserted channel data offset register 3\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`ioff3::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`ioff3::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct Ioff3Spec;
impl crate::RegisterSpec for Ioff3Spec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`ioff3::R`](R) reader structure"]
impl crate::Readable for Ioff3Spec {}
#[doc = "`write(|w| ..)` method takes [`ioff3::W`](W) writer structure"]
impl crate::Writable for Ioff3Spec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets IOFF3 to value 0"]
impl crate::Resettable for Ioff3Spec {
    const RESET_VALUE: u32 = 0;
}
