#[doc = "Register `IOFF2` reader"]
pub type R = crate::R<Ioff2Spec>;
#[doc = "Register `IOFF2` writer"]
pub type W = crate::W<Ioff2Spec>;
#[doc = "Field `IOFF` reader - Data offset for inserted channel 2"]
pub type IoffR = crate::FieldReader<u16>;
#[doc = "Field `IOFF` writer - Data offset for inserted channel 2"]
pub type IoffW<'a, REG> = crate::FieldWriter<'a, REG, 12, u16>;
impl R {
    #[doc = "Bits 0:11 - Data offset for inserted channel 2"]
    #[inline(always)]
    pub fn ioff(&self) -> IoffR {
        IoffR::new((self.bits & 0x0fff) as u16)
    }
}
impl W {
    #[doc = "Bits 0:11 - Data offset for inserted channel 2"]
    #[inline(always)]
    #[must_use]
    pub fn ioff(&mut self) -> IoffW<Ioff2Spec> {
        IoffW::new(self, 0)
    }
}
#[doc = "Inserted channel data offset register 2\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`ioff2::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`ioff2::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct Ioff2Spec;
impl crate::RegisterSpec for Ioff2Spec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`ioff2::R`](R) reader structure"]
impl crate::Readable for Ioff2Spec {}
#[doc = "`write(|w| ..)` method takes [`ioff2::W`](W) writer structure"]
impl crate::Writable for Ioff2Spec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets IOFF2 to value 0"]
impl crate::Resettable for Ioff2Spec {
    const RESET_VALUE: u32 = 0;
}
