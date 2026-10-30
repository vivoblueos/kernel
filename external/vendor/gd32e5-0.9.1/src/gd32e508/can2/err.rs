#[doc = "Register `ERR` reader"]
pub type R = crate::R<ErrSpec>;
#[doc = "Register `ERR` writer"]
pub type W = crate::W<ErrSpec>;
#[doc = "Field `WERR` reader - Warning error"]
pub type WerrR = crate::BitReader;
#[doc = "Field `PERR` reader - Passive error"]
pub type PerrR = crate::BitReader;
#[doc = "Field `BOERR` reader - Bus-off error"]
pub type BoerrR = crate::BitReader;
#[doc = "Field `ERRN` reader - Error number"]
pub type ErrnR = crate::FieldReader;
#[doc = "Field `ERRN` writer - Error number"]
pub type ErrnW<'a, REG> = crate::FieldWriter<'a, REG, 3>;
#[doc = "Field `TECNT` reader - Transmit Error Count defined by the CAN standard"]
pub type TecntR = crate::FieldReader;
#[doc = "Field `RECNT` reader - Receive Error Count defined by the CAN standard"]
pub type RecntR = crate::FieldReader;
impl R {
    #[doc = "Bit 0 - Warning error"]
    #[inline(always)]
    pub fn werr(&self) -> WerrR {
        WerrR::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - Passive error"]
    #[inline(always)]
    pub fn perr(&self) -> PerrR {
        PerrR::new(((self.bits >> 1) & 1) != 0)
    }
    #[doc = "Bit 2 - Bus-off error"]
    #[inline(always)]
    pub fn boerr(&self) -> BoerrR {
        BoerrR::new(((self.bits >> 2) & 1) != 0)
    }
    #[doc = "Bits 4:6 - Error number"]
    #[inline(always)]
    pub fn errn(&self) -> ErrnR {
        ErrnR::new(((self.bits >> 4) & 7) as u8)
    }
    #[doc = "Bits 16:23 - Transmit Error Count defined by the CAN standard"]
    #[inline(always)]
    pub fn tecnt(&self) -> TecntR {
        TecntR::new(((self.bits >> 16) & 0xff) as u8)
    }
    #[doc = "Bits 24:31 - Receive Error Count defined by the CAN standard"]
    #[inline(always)]
    pub fn recnt(&self) -> RecntR {
        RecntR::new(((self.bits >> 24) & 0xff) as u8)
    }
}
impl W {
    #[doc = "Bits 4:6 - Error number"]
    #[inline(always)]
    #[must_use]
    pub fn errn(&mut self) -> ErrnW<ErrSpec> {
        ErrnW::new(self, 4)
    }
}
#[doc = "Error register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`err::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`err::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct ErrSpec;
impl crate::RegisterSpec for ErrSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`err::R`](R) reader structure"]
impl crate::Readable for ErrSpec {}
#[doc = "`write(|w| ..)` method takes [`err::W`](W) writer structure"]
impl crate::Writable for ErrSpec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets ERR to value 0"]
impl crate::Resettable for ErrSpec {
    const RESET_VALUE: u32 = 0;
}
