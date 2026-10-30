//! Floating-point Status Control Register

/// Floating-point Status Control Register
#[derive(Clone, Copy, Debug)]
pub struct Fpscr {
    bits: u32,
}

impl Fpscr {
    /// Creates a `Fspcr` value from raw bits.
    #[inline]
    pub fn from_bits(bits: u32) -> Self {
        Self { bits }
    }

    /// Returns the contents of the register as raw bits
    #[inline]
    pub fn bits(self) -> u32 {
        self.bits
    }

    /// Read the Negative condition code flag
    #[inline]
    pub fn n(self) -> bool {
        self.bits & (1 << 31) != 0
    }

    /// Sets the Negative condition code flag
    #[inline]
    pub fn set_n(&mut self, n: bool) {
        let mask = 1 << 31;
        match n {
            true => self.bits |= mask,
            false => self.bits &= !mask,
        }
    }

    /// Read the Zero condition code flag
    #[inline]
    pub fn z(self) -> bool {
        self.bits & (1 << 30) != 0
    }

    /// Sets the Zero condition code flag
    #[inline]
    pub fn set_z(&mut self, z: bool) {
        let mask = 1 << 30;
        match z {
            true => self.bits |= mask,
            false => self.bits &= !mask,
        }
    }

    /// Read the Carry condition code flag
    #[inline]
    pub fn c(self) -> bool {
        self.bits & (1 << 29) != 0
    }

    /// Sets the Carry condition code flag
    #[inline]
    pub fn set_c(&mut self, c: bool) {
        let mask = 1 << 29;
        match c {
            true => self.bits |= mask,
            false => self.bits &= !mask,
        }
    }

    /// Read the Overflow condition code flag
    #[inline]
    pub fn v(self) -> bool {
        self.bits & (1 << 28) != 0
    }

    /// Sets the Zero condition code flag
    #[inline]
    pub fn set_v(&mut self, v: bool) {
        let mask = 1 << 28;
        match v {
            true => self.bits |= mask,
            false => self.bits &= !mask,
        }
    }

    /// Read the Alternative Half Precision bit
    #[inline]
    pub fn ahp(self) -> bool {
        self.bits & (1 << 26) != 0
    }

    /// Sets the Alternative Half Precision bit
    #[inline]
    pub fn set_ahp(&mut self, ahp: bool) {
        let mask = 1 << 26;
        match ahp {
            true => self.bits |= mask,
            false => self.bits &= !mask,
        }
    }

    /// Read the Default NaN mode bit
    #[inline]
    pub fn dn(self) -> bool {
        self.bits & (1 << 25) != 0
    }

    /// Sets the Default NaN mode bit
    #[inline]
    pub fn set_dn(&mut self, dn: bool) {
        let mask = 1 << 25;
        match dn {
            true => self.bits |= mask,
            false => self.bits &= !mask,
        }
    }

    /// Read the Flush to Zero mode bit
    #[inline]
    pub fn fz(self) -> bool {
        self.bits & (1 << 24) != 0
    }

    /// Sets the Flush to Zero mode bit
    #[inline]
    pub fn set_fz(&mut self, fz: bool) {
        let mask = 1 << 24;
        match fz {
            true => self.bits |= mask,
            false => self.bits &= !mask,
        }
    }

    /// Read the Rounding Mode control field
    #[inline]
    pub fn rmode(self) -> RMode {
        match (self.bits & (3 << 22)) >> 22 {
            0 => RMode::Nearest,
            1 => RMode::PlusInfinity,
            2 => RMode::MinusInfinity,
            _ => RMode::Zero,
        }
    }

    /// Sets the Rounding Mode control field
    #[inline]
    pub fn set_rmode(&mut self, rmode: RMode) {
        let mask = 3 << 22;
        match rmode {
            RMode::Nearest => self.bits &= !mask,
            RMode::PlusInfinity => self.bits = (self.bits & !mask) | (1 << 22),
            RMode::MinusInfinity => self.bits = (self.bits & !mask) | (2 << 22),
            RMode::Zero => self.bits |= mask,
        }
    }

    /// Read the Input Denormal cumulative exception bit
    #[inline]
    pub fn idc(self) -> bool {
        self.bits & (1 << 7) != 0
    }

    /// Sets the Input Denormal cumulative exception bit
    #[inline]
    pub fn set_idc(&mut self, idc: bool) {
        let mask = 1 << 7;
        match idc {
            true => self.bits |= mask,
            false => self.bits &= !mask,
        }
    }

    /// Read the Inexact cumulative exception bit
    #[inline]
    pub fn ixc(self) -> bool {
        self.bits & (1 << 4) != 0
    }

    /// Sets the Inexact cumulative exception bit
    #[inline]
    pub fn set_ixc(&mut self, ixc: bool) {
        let mask = 1 << 4;
        match ixc {
            true => self.bits |= mask,
            false => self.bits &= !mask,
        }
    }

    /// Read the Underflow cumulative exception bit
    #[inline]
    pub fn ufc(self) -> bool {
        self.bits & (1 << 3) != 0
    }

    /// Sets the Underflow cumulative exception bit
    #[inline]
    pub fn set_ufc(&mut self, ufc: bool) {
        let mask = 1 << 3;
        match ufc {
            true => self.bits |= mask,
            false => self.bits &= !mask,
        }
    }

    /// Read the Overflow cumulative exception bit
    #[inline]
    pub fn ofc(self) -> bool {
        self.bits & (1 << 2) != 0
    }

    /// Sets the Overflow cumulative exception bit
    #[inline]
    pub fn set_ofc(&mut self, ofc: bool) {
        let mask = 1 << 2;
        match ofc {
            true => self.bits |= mask,
            false => self.bits &= !mask,
        }
    }

    /// Read the Division by Zero cumulative exception bit
    #[inline]
    pub fn dzc(self) -> bool {
        self.bits & (1 << 1) != 0
    }

    /// Sets the Division by Zero cumulative exception bit
    #[inline]
    pub fn set_dzc(&mut self, dzc: bool) {
        let mask = 1 << 1;
        match dzc {
            true => self.bits |= mask,
            false => self.bits &= !mask,
        }
    }

    /// Read the Invalid Operation cumulative exception bit
    #[inline]
    pub fn ioc(self) -> bool {
        self.bits & (1 << 0) != 0
    }

    /// Sets the Invalid Operation cumulative exception bit
    #[inline]
    pub fn set_ioc(&mut self, ioc: bool) {
        let mask = 1 << 0;
        match ioc {
            true => self.bits |= mask,
            false => self.bits &= !mask,
        }
    }
}

/// Rounding mode
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum RMode {
    /// Round to Nearest (RN) mode. This is the reset value.
    Nearest,
    /// Round towards Plus Infinity (RP) mode.
    PlusInfinity,
    /// Round towards Minus Infinity (RM) mode.
    MinusInfinity,
    /// Round towards Zero (RZ) mode.
    Zero,
}

impl RMode {
    /// Is Nearest the current rounding mode?
    #[inline]
    pub fn is_nearest(self) -> bool {
        self == RMode::Nearest
    }

    /// Is Plus Infinity the current rounding mode?
    #[inline]
    pub fn is_plus_infinity(self) -> bool {
        self == RMode::PlusInfinity
    }

    /// Is Minus Infinity the current rounding mode?
    #[inline]
    pub fn is_minus_infinity(self) -> bool {
        self == RMode::MinusInfinity
    }

    /// Is Zero the current rounding mode?
    #[inline]
    pub fn is_zero(self) -> bool {
        self == RMode::Zero
    }
}

/// Read the FPSCR register
#[inline]
pub fn read() -> Fpscr {
    let r: u32 = call_asm!(__fpscr_r() -> u32);
    Fpscr::from_bits(r)
}

/// Set the value of the FPSCR register
#[inline]
pub unsafe fn write(fpscr: Fpscr) {
    let fpscr = fpscr.bits();
    call_asm!(__fpscr_w(fpscr: u32));
}
