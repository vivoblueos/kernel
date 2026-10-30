use crate::repr::EnumSetTypeRepr;

pub trait Primitive {
    fn leading_zeros(&self) -> u32;
    fn trailing_zeros(&self) -> u32;
}

macro_rules! prim {
    ($name:ty, $width:expr, $preferred_array_len:expr) => {
        const _: () = {
            fn lo(v: $name) -> u64 {
                v as u64
            }
            fn hi(v: $name) -> u64 {
                ((v as u128) >> 64) as u64
            }

            impl EnumSetTypeRepr for $name {
                const PREFERRED_ARRAY_LEN: usize = $preferred_array_len;
                const WIDTH: u32 = $width;
                const EMPTY: Self = 0;

                #[inline(always)]
                fn is_empty(&self) -> bool {
                    *self == 0
                }

                #[inline(always)]
                fn add_bit(&mut self, bit: u32) {
                    *self |= 1 << bit as $name;
                }
                #[inline(always)]
                fn remove_bit(&mut self, bit: u32) {
                    *self &= !(1 << bit as $name);
                }
                #[inline(always)]
                fn has_bit(&self, bit: u32) -> bool {
                    (self & (1 << bit as $name)) != 0
                }

                #[inline(always)]
                fn count_ones(&self) -> u32 {
                    (*self).count_ones()
                }

                #[inline(always)]
                fn and_not(&self, other: Self) -> Self {
                    (*self) & !other
                }

                type Iter = PrimitiveIter<Self>;
                #[inline]
                fn iter(self) -> Self::Iter {
                    PrimitiveIter(self)
                }

                #[inline(always)]
                fn from_u8(v: u8) -> Self {
                    v as $name
                }
                #[inline(always)]
                fn from_u16(v: u16) -> Self {
                    v as $name
                }
                #[inline(always)]
                fn from_u32(v: u32) -> Self {
                    v as $name
                }
                #[inline(always)]
                fn from_u64(v: u64) -> Self {
                    v as $name
                }
                #[inline(always)]
                fn from_u128(v: u128) -> Self {
                    v as $name
                }
                #[inline(always)]
                fn from_usize(v: usize) -> Self {
                    v as $name
                }

                #[inline(always)]
                fn to_u8(&self) -> u8 {
                    (*self) as u8
                }
                #[inline(always)]
                fn to_u16(&self) -> u16 {
                    (*self) as u16
                }
                #[inline(always)]
                fn to_u32(&self) -> u32 {
                    (*self) as u32
                }
                #[inline(always)]
                fn to_u64(&self) -> u64 {
                    (*self) as u64
                }
                #[inline(always)]
                fn to_u128(&self) -> u128 {
                    (*self) as u128
                }
                #[inline(always)]
                fn to_usize(&self) -> usize {
                    (*self) as usize
                }

                #[inline(always)]
                fn try_from_u8(v: u8) -> Option<Self> {
                    v.try_into().ok()
                }
                #[inline(always)]
                fn try_from_u16(v: u16) -> Option<Self> {
                    v.try_into().ok()
                }
                #[inline(always)]
                fn try_from_u32(v: u32) -> Option<Self> {
                    v.try_into().ok()
                }
                #[inline(always)]
                fn try_from_u64(v: u64) -> Option<Self> {
                    v.try_into().ok()
                }
                #[inline(always)]
                fn try_from_u128(v: u128) -> Option<Self> {
                    v.try_into().ok()
                }
                #[inline(always)]
                fn try_from_usize(v: usize) -> Option<Self> {
                    v.try_into().ok()
                }

                #[inline(always)]
                fn try_to_u8(&self) -> Option<u8> {
                    (*self).try_into().ok()
                }
                #[inline(always)]
                fn try_to_u16(&self) -> Option<u16> {
                    (*self).try_into().ok()
                }
                #[inline(always)]
                fn try_to_u32(&self) -> Option<u32> {
                    (*self).try_into().ok()
                }
                #[inline(always)]
                fn try_to_u64(&self) -> Option<u64> {
                    (*self).try_into().ok()
                }
                #[inline(always)]
                fn try_to_u128(&self) -> Option<u128> {
                    (*self).try_into().ok()
                }
                #[inline(always)]
                fn try_to_usize(&self) -> Option<usize> {
                    (*self).try_into().ok()
                }

                #[inline(always)]
                fn to_u64_array<const O: usize>(&self) -> [u64; O] {
                    let mut array = [0; O];
                    if O > 0 {
                        array[0] = lo(*self);
                    }
                    if O > 1 && $preferred_array_len == 2 {
                        array[1] = hi(*self);
                    }
                    array
                }
                #[inline(always)]
                fn try_to_u64_array<const O: usize>(&self) -> Option<[u64; O]> {
                    if O == 0 && *self != 0 {
                        None
                    } else if O == 1 && hi(*self) != 0 {
                        None
                    } else {
                        Some(self.to_u64_array())
                    }
                }

                #[inline(always)]
                fn from_u64_array<const O: usize>(v: [u64; O]) -> Self {
                    if O == 0 {
                        0
                    } else if O > 1 && $preferred_array_len == 2 {
                        Self::from_u128(v[0] as u128 | ((v[1] as u128) << 64))
                    } else {
                        Self::from_u64(v[0])
                    }
                }
                #[inline(always)]
                fn try_from_u64_array<const O: usize>(v: [u64; O]) -> Option<Self> {
                    if O == 0 {
                        Some(0)
                    } else if O == 1 {
                        Self::try_from_u64(v[0])
                    } else {
                        if $preferred_array_len == 1 && v[1] != 0 {
                            return None;
                        }
                        for i in 2..O {
                            if v[i] != 0 {
                                return None;
                            }
                        }
                        Self::try_from_u128(v[0] as u128 | ((v[1] as u128) << 64))
                    }
                }

                #[inline(always)]
                fn to_u64_slice(&self, out: &mut [u64]) {
                    if out.len() > 0 {
                        out[0] = lo(*self);
                    }
                    if out.len() > 1 && $preferred_array_len == 2 {
                        out[1] = hi(*self);
                    }
                    for i in $preferred_array_len..out.len() {
                        out[i] = 0;
                    }
                }
                #[inline(always)]
                fn try_to_u64_slice(&self, out: &mut [u64]) -> Option<()> {
                    if out.len() == 0 && *self != 0 {
                        None
                    } else if out.len() == 1 && hi(*self) != 0 {
                        None
                    } else {
                        self.to_u64_slice(out);
                        Some(())
                    }
                }

                #[inline(always)]
                fn from_u64_slice(v: &[u64]) -> Self {
                    if v.len() == 0 {
                        0
                    } else if v.len() > 1 && $preferred_array_len == 2 {
                        Self::from_u128(v[0] as u128 | ((v[1] as u128) << 64))
                    } else {
                        Self::from_u64(v[0])
                    }
                }
                #[inline(always)]
                fn try_from_u64_slice(v: &[u64]) -> Option<Self> {
                    if v.len() == 0 {
                        Some(0)
                    } else if v.len() == 1 {
                        Self::try_from_u64(v[0])
                    } else {
                        for i in 2..v.len() {
                            if v[i] != 0 {
                                return None;
                            }
                        }
                        Self::try_from_u128(v[0] as u128 | ((v[1] as u128) << 64))
                    }
                }
            }
            impl Primitive for $name {
                #[inline(always)]
                fn leading_zeros(&self) -> u32 {
                    (*self).leading_zeros()
                }
                #[inline(always)]
                fn trailing_zeros(&self) -> u32 {
                    (*self).trailing_zeros()
                }
            }
        };
    };
}
prim!(u8, 8, 1);
prim!(u16, 16, 1);
prim!(u32, 32, 1);
prim!(u64, 64, 1);
prim!(u128, 128, 2);

#[derive(Copy, Clone, Debug)]
#[repr(transparent)]
pub struct PrimitiveIter<T: EnumSetTypeRepr + Primitive>(pub T);

impl<T: EnumSetTypeRepr + Primitive> Iterator for PrimitiveIter<T> {
    type Item = u32;

    fn next(&mut self) -> Option<Self::Item> {
        if self.0.is_empty() {
            None
        } else {
            let bit = self.0.trailing_zeros();
            self.0.remove_bit(bit);
            Some(bit)
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let left = self.0.count_ones() as usize;
        (left, Some(left))
    }
}

impl<T: EnumSetTypeRepr + Primitive> DoubleEndedIterator for PrimitiveIter<T> {
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.0.is_empty() {
            None
        } else {
            let bit = T::WIDTH - 1 - self.0.leading_zeros();
            self.0.remove_bit(bit);
            Some(bit)
        }
    }
}

impl<T: EnumSetTypeRepr + Primitive> ExactSizeIterator for PrimitiveIter<T> {}
