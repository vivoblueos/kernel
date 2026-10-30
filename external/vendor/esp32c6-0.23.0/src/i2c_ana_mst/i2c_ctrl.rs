#[doc = "Register `I2C%s_CTRL` reader"]
pub type R = crate::R<I2C_CTRL_SPEC>;
#[doc = "Register `I2C%s_CTRL` writer"]
pub type W = crate::W<I2C_CTRL_SPEC>;
#[doc = "Field `SLAVE_ADDR` reader - Configures the slave address"]
pub type SLAVE_ADDR_R = crate::FieldReader;
#[doc = "Field `SLAVE_ADDR` writer - Configures the slave address"]
pub type SLAVE_ADDR_W<'a, REG> = crate::FieldWriter<'a, REG, 8>;
#[doc = "Field `SLAVE_REG_ADDR` reader - Configures the slave register address"]
pub type SLAVE_REG_ADDR_R = crate::FieldReader;
#[doc = "Field `SLAVE_REG_ADDR` writer - Configures the slave register address"]
pub type SLAVE_REG_ADDR_W<'a, REG> = crate::FieldWriter<'a, REG, 8>;
#[doc = "Field `DATA` reader - Configures the transmitted data"]
pub type DATA_R = crate::FieldReader;
#[doc = "Field `DATA` writer - Configures the transmitted data"]
pub type DATA_W<'a, REG> = crate::FieldWriter<'a, REG, 8>;
#[doc = "Field `READ_WRITE` reader - Configures the read/write operation"]
pub type READ_WRITE_R = crate::BitReader;
#[doc = "Field `READ_WRITE` writer - Configures the read/write operation"]
pub type READ_WRITE_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `BUSY` reader - Represents whether I2C0 is currently transferring data"]
pub type BUSY_R = crate::BitReader;
impl R {
    #[doc = "Bits 0:7 - Configures the slave address"]
    #[inline(always)]
    pub fn slave_addr(&self) -> SLAVE_ADDR_R {
        SLAVE_ADDR_R::new((self.bits & 0xff) as u8)
    }
    #[doc = "Bits 8:15 - Configures the slave register address"]
    #[inline(always)]
    pub fn slave_reg_addr(&self) -> SLAVE_REG_ADDR_R {
        SLAVE_REG_ADDR_R::new(((self.bits >> 8) & 0xff) as u8)
    }
    #[doc = "Bits 16:23 - Configures the transmitted data"]
    #[inline(always)]
    pub fn data(&self) -> DATA_R {
        DATA_R::new(((self.bits >> 16) & 0xff) as u8)
    }
    #[doc = "Bit 24 - Configures the read/write operation"]
    #[inline(always)]
    pub fn read_write(&self) -> READ_WRITE_R {
        READ_WRITE_R::new(((self.bits >> 24) & 1) != 0)
    }
    #[doc = "Bit 25 - Represents whether I2C0 is currently transferring data"]
    #[inline(always)]
    pub fn busy(&self) -> BUSY_R {
        BUSY_R::new(((self.bits >> 25) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("I2C_CTRL")
            .field("slave_addr", &self.slave_addr())
            .field("slave_reg_addr", &self.slave_reg_addr())
            .field("data", &self.data())
            .field("read_write", &self.read_write())
            .field("busy", &self.busy())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:7 - Configures the slave address"]
    #[inline(always)]
    pub fn slave_addr(&mut self) -> SLAVE_ADDR_W<'_, I2C_CTRL_SPEC> {
        SLAVE_ADDR_W::new(self, 0)
    }
    #[doc = "Bits 8:15 - Configures the slave register address"]
    #[inline(always)]
    pub fn slave_reg_addr(&mut self) -> SLAVE_REG_ADDR_W<'_, I2C_CTRL_SPEC> {
        SLAVE_REG_ADDR_W::new(self, 8)
    }
    #[doc = "Bits 16:23 - Configures the transmitted data"]
    #[inline(always)]
    pub fn data(&mut self) -> DATA_W<'_, I2C_CTRL_SPEC> {
        DATA_W::new(self, 16)
    }
    #[doc = "Bit 24 - Configures the read/write operation"]
    #[inline(always)]
    pub fn read_write(&mut self) -> READ_WRITE_W<'_, I2C_CTRL_SPEC> {
        READ_WRITE_W::new(self, 24)
    }
}
#[doc = "I2C%s_CTRL register\n\nYou can [`read`](crate::Reg::read) this register and get [`i2c_ctrl::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`i2c_ctrl::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct I2C_CTRL_SPEC;
impl crate::RegisterSpec for I2C_CTRL_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`i2c_ctrl::R`](R) reader structure"]
impl crate::Readable for I2C_CTRL_SPEC {}
#[doc = "`write(|w| ..)` method takes [`i2c_ctrl::W`](W) writer structure"]
impl crate::Writable for I2C_CTRL_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets I2C%s_CTRL to value 0"]
impl crate::Resettable for I2C_CTRL_SPEC {}
