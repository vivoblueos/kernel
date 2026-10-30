#[doc = "Register `IOFF0` reader"]
pub type R = crate::R<Ioff0Spec>;
#[doc = "Register `IOFF0` writer"]
pub type W = crate::W<Ioff0Spec>;
#[doc = "Field `IOFF` reader - Data offset for inserted channel 0"]
pub type IoffR = crate::FieldReader<u16>;
#[doc = "Field `IOFF` writer - Data offset for inserted channel 0"]
pub type IoffW<'a, REG> = crate::FieldWriter<'a, REG, 12, u16>;
impl R {
    #[doc = "Bits 0:11 - Data offset for inserted channel 0"]
    #[inline(always)]
    pub fn ioff(&self) -> IoffR {
        IoffR::new((self.bits & 0x0fff) as u16)
    }
}
impl W {
    #[doc = "Bits 0:11 - Data offset for inserted channel 0"]
    #[inline(always)]
    #[must_use]
    pub fn ioff(&mut self) -> IoffW<Ioff0Spec> {
        IoffW::new(self, 0)
    }
}
#[doc = "Inserted channel data offset register 0\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`ioff0::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`ioff0::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct Ioff0Spec;
impl crate::RegisterSpec for Ioff0Spec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`ioff0::R`](R) reader structure"]
impl crate::Readable for Ioff0Spec {}
#[doc = "`write(|w| ..)` method takes [`ioff0::W`](W) writer structure"]
impl crate::Writable for Ioff0Spec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets IOFF0 to value 0"]
impl crate::Resettable for Ioff0Spec {
    const RESET_VALUE: u32 = 0;
}
