use crate::repr::primitive::PrimitiveIter;
use crate::repr::EnumSetTypeRepr;
use core::ops::*;

/// An implementation of `EnumSetTypeRepr` based on an arbitrary size array.
///
/// `N` **must** not be `0`, or else everything will break.
#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Debug, Hash)]
pub struct ArrayRepr<const N: usize>(pub [u64; N]);
impl<const N: usize> ArrayRepr<N> {
    fn split_bit(bit: u32) -> (usize, u32) {
        (bit as usize / 64, bit % 64)
    }
}

impl<const N: usize> BitAnd for ArrayRepr<N> {
    type Output = Self;
    fn bitand(mut self, rhs: Self) -> Self::Output {
        for i in 0..N {
            self.0[i] &= rhs.0[i];
        }
        self
    }
}
impl<const N: usize> BitOr for ArrayRepr<N> {
    type Output = Self;
    fn bitor(mut self, rhs: Self) -> Self::Output {
        for i in 0..N {
            self.0[i] |= rhs.0[i];
        }
        self
    }
}
impl<const N: usize> BitXor for ArrayRepr<N> {
    type Output = Self;
    fn bitxor(mut self, rhs: Self) -> Self::Output {
        for i in 0..N {
            self.0[i] ^= rhs.0[i];
        }
        self
    }
}
impl<const N: usize> Not for ArrayRepr<N> {
    type Output = Self;
    fn not(mut self) -> Self::Output {
        for i in 0..N {
            self.0[i] = !self.0[i];
        }
        self
    }
}

impl<const N: usize> EnumSetTypeRepr for ArrayRepr<N> {
    const PREFERRED_ARRAY_LEN: usize = N;
    const WIDTH: u32 = N as u32 * 64;
    const EMPTY: Self = ArrayRepr([0; N]);

    fn is_empty(&self) -> bool {
        self.0.iter().all(|x| *x == 0)
    }

    fn add_bit(&mut self, bit: u32) {
        let (idx, bit) = Self::split_bit(bit);
        self.0[idx].add_bit(bit);
    }
    fn remove_bit(&mut self, bit: u32) {
        let (idx, bit) = Self::split_bit(bit);
        self.0[idx].remove_bit(bit);
    }
    fn has_bit(&self, bit: u32) -> bool {
        let (idx, bit) = Self::split_bit(bit);
        self.0[idx].has_bit(bit)
    }

    fn count_ones(&self) -> u32 {
        self.0.iter().map(|x| x.count_ones()).sum()
    }

    fn and_not(&self, other: Self) -> Self {
        let mut new = Self([0; N]);
        for i in 0..N {
            new.0[i] = self.0[i] & !other.0[i];
        }
        new
    }

    type Iter = ArrayIter<N>;
    fn iter(self) -> Self::Iter {
        ArrayIter::new(self)
    }

    fn from_u8(v: u8) -> Self {
        Self::from_u64(v as u64)
    }
    fn from_u16(v: u16) -> Self {
        Self::from_u64(v as u64)
    }
    fn from_u32(v: u32) -> Self {
        Self::from_u64(v as u64)
    }
    fn from_u64(v: u64) -> Self {
        let mut new = Self([0; N]);
        new.0[0] = v;
        new
    }
    fn from_u128(v: u128) -> Self {
        let mut new = Self([0; N]);
        new.0[0] = v as u64;
        if N != 1 {
            new.0[1] = (v >> 64) as u64;
        }
        new
    }
    fn from_usize(v: usize) -> Self {
        Self::from_u64(v as u64)
    }

    fn try_from_u8(v: u8) -> Option<Self> {
        Some(Self::from_u8(v))
    }
    fn try_from_u16(v: u16) -> Option<Self> {
        Some(Self::from_u16(v))
    }
    fn try_from_u32(v: u32) -> Option<Self> {
        Some(Self::from_u32(v))
    }
    fn try_from_u64(v: u64) -> Option<Self> {
        Some(Self::from_u64(v))
    }
    fn try_from_u128(v: u128) -> Option<Self> {
        if N == 1 && (v >> 64) != 0 {
            None
        } else {
            Some(Self::from_u128(v))
        }
    }
    fn try_from_usize(v: usize) -> Option<Self> {
        Some(Self::from_usize(v))
    }

    fn to_u8(&self) -> u8 {
        self.to_u64().to_u8()
    }
    fn to_u16(&self) -> u16 {
        self.to_u64().to_u16()
    }
    fn to_u32(&self) -> u32 {
        self.to_u64().to_u32()
    }
    fn to_u64(&self) -> u64 {
        self.0[0]
    }
    fn to_u128(&self) -> u128 {
        let hi = if N == 1 { 0 } else { (self.0[1] as u128) << 64 };
        self.0[0] as u128 | hi
    }
    fn to_usize(&self) -> usize {
        self.to_u64().to_usize()
    }

    fn try_to_u8(&self) -> Option<u8> {
        self.try_to_u64().and_then(|x| x.try_to_u8())
    }
    fn try_to_u16(&self) -> Option<u16> {
        self.try_to_u64().and_then(|x| x.try_to_u16())
    }
    fn try_to_u32(&self) -> Option<u32> {
        self.try_to_u64().and_then(|x| x.try_to_u32())
    }
    fn try_to_u64(&self) -> Option<u64> {
        for i in 1..N {
            if self.0[i] != 0 {
                return None;
            }
        }
        Some(self.to_u64())
    }
    fn try_to_u128(&self) -> Option<u128> {
        for i in 2..N {
            if self.0[i] != 0 {
                return None;
            }
        }
        Some(self.to_u128())
    }
    fn try_to_usize(&self) -> Option<usize> {
        self.try_to_u64().and_then(|x| x.try_to_usize())
    }

    fn to_u64_array<const O: usize>(&self) -> [u64; O] {
        let mut array = [0; O];
        let copy_len = if N < O { N } else { O };
        array[..copy_len].copy_from_slice(&self.0[..copy_len]);
        array
    }
    fn try_to_u64_array<const O: usize>(&self) -> Option<[u64; O]> {
        if N > O {
            for i in O..N {
                if self.0[i] != 0 {
                    return None;
                }
            }
        }
        Some(self.to_u64_array())
    }

    fn from_u64_array<const O: usize>(v: [u64; O]) -> Self {
        ArrayRepr(ArrayRepr::<O>(v).to_u64_array::<N>())
    }
    fn try_from_u64_array<const O: usize>(v: [u64; O]) -> Option<Self> {
        ArrayRepr::<O>(v).try_to_u64_array::<N>().map(ArrayRepr)
    }

    fn to_u64_slice(&self, out: &mut [u64]) {
        let copy_len = if N < out.len() { N } else { out.len() };
        out[..copy_len].copy_from_slice(&self.0[..copy_len]);
        for i in copy_len..out.len() {
            out[i] = 0;
        }
    }
    fn try_to_u64_slice(&self, out: &mut [u64]) -> Option<()> {
        if N > out.len() {
            for i in out.len()..N {
                if self.0[i] != 0 {
                    return None;
                }
            }
        }
        self.to_u64_slice(out);
        Some(())
    }

    fn from_u64_slice(v: &[u64]) -> Self {
        let mut new = ArrayRepr([0; N]);
        let copy_len = if N < v.len() { N } else { v.len() };
        new.0[..copy_len].copy_from_slice(&v[..copy_len]);
        new
    }
    fn try_from_u64_slice(v: &[u64]) -> Option<Self> {
        if v.len() > N {
            for i in N..v.len() {
                if v[i] != 0 {
                    return None;
                }
            }
        }
        Some(Self::from_u64_slice(v))
    }
}

#[derive(Clone, Debug)]
pub struct ArrayIter<const N: usize> {
    data: [PrimitiveIter<u64>; N],
    done: bool,
    idx_f: usize,
    idx_r: usize,
}

impl<const N: usize> ArrayIter<N> {
    fn new(array: ArrayRepr<N>) -> Self {
        let mut new = [PrimitiveIter(0); N];
        for i in 0..N {
            new[i] = PrimitiveIter(array.0[i])
        }
        ArrayIter { data: new, done: false, idx_f: 0, idx_r: N - 1 }
    }
}

impl<const N: usize> Iterator for ArrayIter<N> {
    type Item = u32;

    fn next(&mut self) -> Option<Self::Item> {
        if self.done {
            return None;
        }
        loop {
            if let Some(x) = unsafe { self.data.get_unchecked_mut(self.idx_f).next() } {
                return Some(self.idx_f as u32 * 64 + x);
            } else {
                if self.idx_f == N - 1 || self.idx_f > self.idx_r {
                    break;
                }
                self.idx_f += 1;
            }
        }
        self.done = true;
        None
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let mut sum = 0;
        for i in self.idx_f..self.idx_r + 1 {
            sum += self.data[i].0.count_ones() as usize;
        }
        (sum, Some(sum))
    }
}

impl<const N: usize> DoubleEndedIterator for ArrayIter<N> {
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.done {
            return None;
        }
        loop {
            if let Some(x) = unsafe { self.data.get_unchecked_mut(self.idx_r).next_back() } {
                return Some(self.idx_r as u32 * 64 + x);
            } else {
                if self.idx_r == 0 || self.idx_f > self.idx_r {
                    break;
                }
                self.idx_r -= 1;
            }
        }
        self.done = true;
        None
    }
}
