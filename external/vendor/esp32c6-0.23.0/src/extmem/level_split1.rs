#[doc = "Register `LEVEL_SPLIT1` reader"]
pub type R = crate::R<LEVEL_SPLIT1_SPEC>;
#[doc = "Field `LEVEL_SPLIT1` reader - Reserved"]
pub type LEVEL_SPLIT1_R = crate::FieldReader<u32>;
impl R {
    #[doc = "Bits 0:31 - Reserved"]
    #[inline(always)]
    pub fn level_split1(&self) -> LEVEL_SPLIT1_R {
        LEVEL_SPLIT1_R::new(self.bits)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("LEVEL_SPLIT1")
            .field("level_split1", &self.level_split1())
            .finish()
    }
}
#[doc = "USED TO SPLIT L1 CACHE AND L2 CACHE\n\nYou can [`read`](crate::Reg::read) this register and get [`level_split1::R`](R). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct LEVEL_SPLIT1_SPEC;
impl crate::RegisterSpec for LEVEL_SPLIT1_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`level_split1::R`](R) reader structure"]
impl crate::Readable for LEVEL_SPLIT1_SPEC {}
#[doc = "`reset()` method sets LEVEL_SPLIT1 to value 0x03a8"]
impl crate::Resettable for LEVEL_SPLIT1_SPEC {
    const RESET_VALUE: u32 = 0x03a8;
}
