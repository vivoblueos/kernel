// Copyright © 2019–2021 Trevor Spiteri

// This library is free software: you can redistribute it and/or
// modify it under the terms of either
//
//   * the Apache License, Version 2.0 or
//   * the MIT License
//
// at your option.
//
// You should have recieved copies of the Apache License and the MIT
// License along with the library. If not, see
// <https://www.apache.org/licenses/LICENSE-2.0> and
// <https://opensource.org/licenses/MIT>.

use crate::{cast, Cast, CheckedCast, Round, UnwrappedCast};
use core::fmt::{Debug, Display, Formatter, LowerExp, Result as FmtResult, UpperExp};

macro_rules! convert {
    ($($Src:ty),* => $Dst:ty) => { $(
        impl Cast<$Dst> for $Src {
            #[inline]
            fn cast(self) -> $Dst {
                self as $Dst
            }
        }

        impl CheckedCast<$Dst> for $Src {
            #[inline]
            fn checked_cast(self) -> Option<$Dst> {
                Some(cast(self))
            }
        }

        impl UnwrappedCast<$Dst> for $Src {
            #[inline]
            fn unwrapped_cast(self) -> $Dst {
                cast(self)
            }
        }
    )* };
}

convert! { i8, i16, i32, i64, i128, isize, u8, u16, u32, u64, u128, usize, f32, f64 => f32 }
convert! { i8, i16, i32, i64, i128, isize, u8, u16, u32, u64, u128, usize, f32, f64 => f64 }

impl<T: Display> Display for Round<T> {
    fn fmt(&self, f: &mut Formatter) -> FmtResult {
        Display::fmt(&self.0, f)
    }
}

impl<T: Debug> Debug for Round<T> {
    fn fmt(&self, f: &mut Formatter) -> FmtResult {
        Debug::fmt(&self.0, f)
    }
}

impl<T: LowerExp> LowerExp for Round<T> {
    fn fmt(&self, f: &mut Formatter) -> FmtResult {
        LowerExp::fmt(&self.0, f)
    }
}

impl<T: UpperExp> UpperExp for Round<T> {
    fn fmt(&self, f: &mut Formatter) -> FmtResult {
        UpperExp::fmt(&self.0, f)
    }
}
