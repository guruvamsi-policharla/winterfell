// Copyright (c) 2022 Cloudflare, Inc. and contributors.
// Licensed under the BSD-3-Clause license found in the LICENSE file or
// at https://opensource.org/licenses/BSD-3-Clause

//! An implementation of a 23-bit prime field with modulus $2^{23} - 2^{20} + 1$.

// TODO
//
//  There is room for improvement:
//
//      1. Add an unsafe "add" that doesn't reduce and use internally in the
//         implementation of the extension fields.
//      2. Choose better extension fields (and add tests for them.)
//      3. Change PositiveInteger to u32
//      4. Check if our broken elements_as_bytes is an issue

use super::{ExtensibleField, FieldElement, StarkField};
use crate::field::CubeExtension;
use core::{
    convert::TryFrom,
    fmt::{Debug, Display, Formatter},
    mem,
    ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Neg, Sub, SubAssign},
    slice,
};
use utils::{
    collections::Vec, string::ToString, AsBytes, ByteReader, ByteWriter, Deserializable,
    DeserializationError, Randomizable, Serializable,
};

#[cfg(test)]
mod tests;

// CONSTANTS
// ================================================================================================

/// Field modulus = 2^23 - 2^20 + 1
const M: u32 = 0x700001;

/// R^2 mod M; this is used for conversion of elements into Montgomery representation.
const R2: u32 = 0x32f054;

/// 2^20 primitive root of unity
const G: u32 = 2187;

/// Number of bytes needed to represent field element
const ELEMENT_BYTES: usize = 3;

// FIELD ELEMENT
// ================================================================================================

/// Represents base field element in the field.
///
/// Internal values are stored in the range [0, 2M). The backing type is `u32`.
#[derive(Copy, Clone, Debug, Default)]
pub struct BaseElement(u32);
impl BaseElement {
    /// Creates a new field element from the provided `value`; the value is converted into
    /// Montgomery representation.
    pub const fn new(value: u32) -> BaseElement {
        Self(mont_red_cst((value as u64) * (R2 as u64)))
    }

    /// Returns a new field element from the provided 'value'. Assumes that 'value' is already
    /// in canonical Montgomery form.
    pub const fn from_mont(value: u32) -> BaseElement {
        BaseElement(value)
    }

    /// Returns the non-canonical u32 inner value.
    pub const fn inner(&self) -> u32 {
        self.0
    }

    /// Computes an exponentiation to the power 7. This is useful for computing Rescue-Prime
    /// S-Box over this field.
    #[inline(always)]
    pub fn exp7(self) -> Self {
        let x2 = self.square();
        let x4 = x2.square();
        let x3 = x2 * self;
        x3 * x4
    }
}

impl FieldElement for BaseElement {
    type PositiveInteger = u64; // TODO can we convert this to u32?
    type BaseField = Self;

    const ZERO: Self = Self::new(0);
    const ONE: Self = Self::new(1);

    const ELEMENT_BYTES: usize = ELEMENT_BYTES;
    const IS_CANONICAL: bool = false;

    #[inline]
    fn double(self) -> Self {
        Self(reduce_le_2m(self.0 + self.0))
    }

    #[inline]
    fn exp(self, power: Self::PositiveInteger) -> Self {
        let mut b: Self;
        let mut r = Self::ONE;
        for i in (0..64).rev() {
            r = r.square();
            b = r;
            b *= self;
            // Constant-time branching
            let mask = -(((power >> i) & 1 == 1) as i32) as u32;
            r.0 ^= mask & (r.0 ^ b.0);
        }

        r
    }

    #[inline]
    #[allow(clippy::many_single_char_names)]
    fn inv(self) -> Self {
        // M-2 = 0x6fffff
        // addchain search 7340031
        // addchain: best: opt(dictionary(sliding_window(32),continued_fractions(dichotomic)))
        //     _10    = 2*1
        //     _11    = 1 + _10
        //     _110   = 2*_11
        //     _11000 = _110 << 2
        //     _11110 = _110 + _11000
        //     x9     = _11110 << 4 + _11110 + 1
        //     i15    = 2*x9 + x9 + _11
        //     x11    = x9 + i15
        //     return   (i15 + x11) << 11 + x11
        let x11 = exp_acc::<1>(self, self);
        let x110 = x11.square();
        let x11110 = exp_acc::<2>(x110, x110);
        let x9 = exp_acc::<4>(x11110, x11110) * self;
        let i15 = exp_acc::<1>(x9, x9) * x11;
        let x11 = x9 * i15;
        exp_acc::<11>(i15 * x11, x11)
    }

    fn conjugate(&self) -> Self {
        Self(self.0)
    }

    // TODO We return a slice of length 4*len, whereas bytes_as_elements
    // expects one of length 3*len. The signature of elements_as_bytes prevents
    // us from allocating an array to pack the u32 into 3 bytes.
    fn elements_as_bytes(elements: &[Self]) -> &[u8] {
        // TODO: take endianness into account.
        let p = elements.as_ptr();
        let len = elements.len() * 4;
        unsafe { slice::from_raw_parts(p as *const u8, len) }
    }

    unsafe fn bytes_as_elements(bytes: &[u8]) -> Result<&[Self], DeserializationError> {
        if bytes.len() % Self::ELEMENT_BYTES != 0 {
            return Err(DeserializationError::InvalidValue(format!(
                "number of bytes ({}) does not divide into whole number of field elements",
                bytes.len(),
            )));
        }

        let p = bytes.as_ptr();
        let len = bytes.len() / Self::ELEMENT_BYTES;

        if (p as usize) % mem::align_of::<u32>() != 0 {
            return Err(DeserializationError::InvalidValue(
                "slice memory alignment is not valid for this field element type".to_string(),
            ));
        }

        Ok(slice::from_raw_parts(p as *const Self, len))
    }

    fn zeroed_vector(n: usize) -> Vec<Self> {
        // this uses a specialized vector initialization code which requests zero-filled memory
        // from the OS; unfortunately, this works only for built-in types and we can't use
        // Self::ZERO here as much less efficient initialization procedure will be invoked.
        // We also use u32 to make sure the memory is aligned correctly for our element size.
        let result = vec![0u32; n];

        // translate a zero-filled vector of u32 into a vector of base field elements
        let mut v = core::mem::ManuallyDrop::new(result);
        let p = v.as_mut_ptr();
        let len = v.len();
        let cap = v.capacity();
        unsafe { Vec::from_raw_parts(p as *mut Self, len, cap) }
    }

    fn as_base_elements(elements: &[Self]) -> &[Self::BaseField] {
        elements
    }
}

impl StarkField for BaseElement {
    const MODULUS: Self::PositiveInteger = M as u64;
    const MODULUS_BITS: u32 = 23;
    const GENERATOR: Self = Self::new(3);
    const TWO_ADICITY: u32 = 20;
    const TWO_ADIC_ROOT_OF_UNITY: Self = Self::new(G);

    fn get_modulus_le_bytes() -> Vec<u8> {
        M.to_le_bytes().to_vec()
    }

    #[inline]
    fn as_int(&self) -> Self::PositiveInteger {
        let x = mont_red_cst(self.0 as u64).wrapping_sub(M);
        let mask = ((x as i32) >> 31) as u32; // mask is 2³²-1 if x<0 else 0
        x.wrapping_add(mask & M) as u64
    }
}

impl Randomizable for BaseElement {
    const VALUE_SIZE: usize = ELEMENT_BYTES;

    fn from_random_bytes(source: &[u8]) -> Option<Self> {
        if source.len() >= Self::VALUE_SIZE {
            let value = ((source[2] as u32) << 16) + ((source[1] as u32) << 8) + (source[0] as u32);
            return Some(BaseElement::new(value % M));
        }
        None
    }
}

impl Display for BaseElement {
    fn fmt(&self, f: &mut Formatter) -> core::fmt::Result {
        write!(f, "{}", self.as_int())
    }
}

// EQUALITY CHECKS
// ================================================================================================

impl PartialEq for BaseElement {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        self.as_int() == other.as_int()
    }
}

impl Eq for BaseElement {}

// OVERLOADED OPERATORS
// ================================================================================================

impl Add for BaseElement {
    type Output = Self;

    #[inline]
    #[allow(clippy::suspicious_arithmetic_impl)]
    fn add(self, rhs: Self) -> Self {
        Self(reduce_le_2m(self.0 + rhs.0))
    }
}

impl AddAssign for BaseElement {
    #[inline]
    fn add_assign(&mut self, rhs: Self) {
        *self = *self + rhs
    }
}

impl Sub for BaseElement {
    type Output = Self;

    #[inline]
    #[allow(clippy::suspicious_arithmetic_impl)]
    fn sub(self, rhs: Self) -> Self {
        Self(reduce_le_2m(self.0 + 2 * M - rhs.0))
    }
}

impl SubAssign for BaseElement {
    #[inline]
    fn sub_assign(&mut self, rhs: Self) {
        *self = *self - rhs;
    }
}

impl Mul for BaseElement {
    type Output = Self;

    #[inline]
    fn mul(self, rhs: Self) -> Self {
        Self(mont_red_cst((self.0 as u64) * (rhs.0 as u64)))
    }
}

impl MulAssign for BaseElement {
    #[inline]
    fn mul_assign(&mut self, rhs: Self) {
        *self = *self * rhs
    }
}

impl Div for BaseElement {
    type Output = Self;

    #[inline]
    #[allow(clippy::suspicious_arithmetic_impl)]
    fn div(self, rhs: Self) -> Self {
        self * rhs.inv()
    }
}

impl DivAssign for BaseElement {
    #[inline]
    fn div_assign(&mut self, rhs: Self) {
        *self = *self / rhs
    }
}

impl Neg for BaseElement {
    type Output = Self;

    #[inline]
    fn neg(self) -> Self {
        Self::ZERO - self
    }
}

// QUADRATIC EXTENSION
// ================================================================================================

/// Defines a quadratic extension of the base field over an irreducible polynomial x² + x + 1.
/// Thus, an extension element is defined as α + β * φ, where φ is a root of this polynomial,
/// and α and β are base field elements.
impl ExtensibleField<2> for BaseElement {
    #[inline(always)]
    fn mul(a: [Self; 2], b: [Self; 2]) -> [Self; 2] {
        let a0b0 = a[0] * b[0];
        let a1b1 = a[1] * b[1];
        [
            a0b0 - a1b1,
            ((a[0] + a[1]) * (b[0] + b[1])) - a0b0 - a1b1 - a1b1,
        ]
    }

    #[inline(always)]
    fn mul_base(a: [Self; 2], b: Self) -> [Self; 2] {
        // multiplying an extension field element by a base field element requires just 2
        // multiplications in the base field.
        [a[0] * b, a[1] * b]
    }

    #[inline(always)]
    fn frobenius(x: [Self; 2]) -> [Self; 2] {
        [(x[0] - x[1]), -x[1]]
    }
}

// CUBIC EXTENSION
// ================================================================================================

/// Defines a cubic extension of the base field over an irreducible polynomial x³ + x - 1.
/// Thus, an extension element is defined as α + β * φ + γ * φ², where φ is a root of this
/// polynomial, and α, β and γ are base field elements.
impl ExtensibleField<3> for BaseElement {
    #[inline(always)]
    fn mul(a: [Self; 3], b: [Self; 3]) -> [Self; 3] {
        let x3 = a[2] * b[1] + a[1] * b[2];
        let x4 = a[2] * b[2];
        // TODO We can reduce number of multiplications
        [
            ((a[0] * b[0]) + x3),
            ((a[0] * b[1]) + (a[1] * b[0]) - x3 + x4),
            ((a[0] * b[2]) + (a[1] * b[1]) + (a[2] * b[0]) - x4),
        ]
    }

    #[inline(always)]
    fn mul_base(a: [Self; 3], b: Self) -> [Self; 3] {
        [a[0] * b, a[1] * b, a[2] * b]
    }

    #[inline(always)]
    fn frobenius(x: [Self; 3]) -> [Self; 3] {
        let frobx1 = [Self::new(6987367), Self::new(6546534), Self::new(6811034)];
        let frobx2 = [Self::new(528998), Self::new(7163700), Self::new(793498)];
        let x1 = Self::mul_base(frobx1, x[1]);
        let x2 = Self::mul_base(frobx2, x[2]);
        [(x[0] + x1[0] + x2[0]), (x1[1] + x2[1]), (x1[2] + x2[2])]
    }
}

// SEXTIC EXTENSION = QUADRATIC EXTENSION ON TOP OF A CUBIC EXTENSION
// ================================================================================================

/// Defines a quadratic extension of the cubic extension field using an irreducible polynomial x² + 3.
/// Thus, a sextic extension element is defined as α + β * φ, where φ is a root of this polynomial,
/// and α and β are cubic extension field elements.

impl ExtensibleField<2> for CubeExtension<BaseElement> {
    #[inline(always)]
    fn mul(a: [Self; 2], b: [Self; 2]) -> [Self; 2] {
        let a0b0 = a[0] * b[0];
        let a1b1 = a[1] * b[1];
        [
            a0b0 - a1b1 - a1b1 - a1b1,
            (a[0] + a[1]) * (b[0] + b[1]) - a0b0 - a1b1,
        ]
    }

    #[inline(always)]
    fn mul_base(a: [Self; 2], b: Self) -> [Self; 2] {
        [a[0] * b, a[1] * b]
    }

    #[inline(always)]
    fn frobenius(x: [Self; 2]) -> [Self; 2] {
        [x[0].conjugate(), -x[1].conjugate()]
    }
}

// Implementing the extension Fp^6 as Fp^3[x] / (x^2 + 3).
impl ExtensibleField<6> for BaseElement {
    #[inline(always)]
    fn mul(a: [Self; 6], b: [Self; 6]) -> [Self; 6] {
        let a0 = CubeExtension::new(a[0], a[1], a[2]);
        let a1 = CubeExtension::new(a[3], a[4], a[5]);
        let b0 = CubeExtension::new(b[0], b[1], b[2]);
        let b1 = CubeExtension::new(b[3], b[4], b[5]);
        let c = <CubeExtension<BaseElement> as ExtensibleField<2>>::mul([a0, a1], [b0, b1]);
        let mut y: [BaseElement; 6] = Default::default();
        y.copy_from_slice(
            <CubeExtension<BaseElement> as FieldElement>::as_base_elements(&[c[0], c[1]]),
        );
        y
    }

    #[inline(always)]
    fn mul_base(a: [Self; 6], b: Self) -> [Self; 6] {
        // multiplying an extension field element by a base field element requires just 2
        // multiplications in the cubic extension field.
        [a[0] * b, a[1] * b, a[2] * b, a[3] * b, a[4] * b, a[5] * b]
    }

    #[inline(always)]
    fn frobenius(x: [Self; 6]) -> [Self; 6] {
        // given x = α + β * φ
        // frobenius(x) = frobenius(α) + frobenius(β) * frobenius(φ)
        //              = frobenius(α) - frobenius(β) * φ
        let a0 = CubeExtension::new(x[0], x[1], x[2]);
        let a1 = CubeExtension::new(x[3], x[4], x[5]);
        let c = <CubeExtension<BaseElement> as ExtensibleField<2>>::frobenius([a0, a1]);
        let mut y: [BaseElement; 6] = Default::default();
        y.copy_from_slice(
            <CubeExtension<BaseElement> as FieldElement>::as_base_elements(&[c[0], c[1]]),
        );
        y
    }
}

// TYPE CONVERSIONS
// ================================================================================================

impl From<u128> for BaseElement {
    fn from(x: u128) -> Self {
        // TODO optimize
        Self::new(x as u32)
            + Self::new((x >> 32) as u32) * Self::new(0xffdb7)
            + Self::new((x >> 64) as u32) * Self::new(0x32f054)
            + Self::new((x >> 96) as u32) * Self::new(0x218a2f)
    }
}

impl From<u64> for BaseElement {
    fn from(value: u64) -> Self {
        // TODO optimize
        Self::new(value as u32) + Self::new((value >> 32) as u32) * Self::new(0xffdb7)
    }
}

impl From<u32> for BaseElement {
    fn from(value: u32) -> Self {
        Self::new(value)
    }
}

impl From<u16> for BaseElement {
    fn from(value: u16) -> Self {
        Self::new(value as u32)
    }
}

impl From<u8> for BaseElement {
    fn from(value: u8) -> Self {
        Self::new(value as u32)
    }
}

impl From<[u8; 8]> for BaseElement {
    /// Converts the value encoded in an array of 8 bytes into a field element. The bytes are
    /// assumed to encode the element in the canonical representation in little-endian byte order.
    /// If the value is greater than or equal to the field modulus, modular reduction is silently
    /// performed.
    fn from(bytes: [u8; 8]) -> Self {
        let x = u64::from_le_bytes(bytes);
        Self::from(x)
    }
}

impl<'a> TryFrom<&'a [u8]> for BaseElement {
    type Error = DeserializationError;

    /// Converts a slice of bytes into a field element; returns error if the value encoded in bytes
    /// is not a valid field element. The bytes are assumed to encode the element in the canonical
    /// representation in little-endian byte order.
    fn try_from(bytes: &[u8]) -> Result<Self, Self::Error> {
        if bytes.len() < ELEMENT_BYTES {
            return Err(DeserializationError::InvalidValue(format!(
                "not enough bytes for a full field element; expected {} bytes, but was {} bytes",
                ELEMENT_BYTES,
                bytes.len(),
            )));
        }
        if bytes.len() > ELEMENT_BYTES {
            return Err(DeserializationError::InvalidValue(format!(
                "too many bytes for a field element; expected {} bytes, but was {} bytes",
                ELEMENT_BYTES,
                bytes.len(),
            )));
        }

        let mut buf = [0; 4];
        for (i, bi) in buf.into_iter().enumerate() {
            buf[i] = bi;
        }
        let value = u32::from_le_bytes(buf);
        if value >= M {
            return Err(DeserializationError::InvalidValue(format!(
                "invalid field element: value {} is greater than or equal to the field modulus",
                value
            )));
        }
        Ok(Self::new(value))
    }
}

impl AsBytes for BaseElement {
    fn as_bytes(&self) -> &[u8] {
        // TODO: take endianness into account
        let self_ptr: *const BaseElement = self;
        unsafe { slice::from_raw_parts(self_ptr as *const u8, ELEMENT_BYTES) }
    }
}

// SERIALIZATION / DESERIALIZATION
// ------------------------------------------------------------------------------------------------

impl Serializable for BaseElement {
    fn write_into<W: ByteWriter>(&self, target: &mut W) {
        let bytes = self.as_int().to_le_bytes();
        target.write_u8_slice(&bytes[0..ELEMENT_BYTES]);
    }
}

impl Deserializable for BaseElement {
    fn read_from<R: ByteReader>(source: &mut R) -> Result<Self, DeserializationError> {
        let mut buf = [0; 4];
        let bytes = source.read_u8_vec(ELEMENT_BYTES)?;
        for (i, bi) in bytes.into_iter().enumerate() {
            buf[i] = bi
        }
        let value = u32::from_le_bytes(buf);
        if value >= M {
            return Err(DeserializationError::InvalidValue(format!(
                "invalid field element: value {} is greater than or equal to the field modulus",
                value
            )));
        }
        Ok(Self::new(value))
    }
}

/// Squares the base N number of times and multiplies the result by the tail value.
#[inline(always)]
fn exp_acc<const N: usize>(base: BaseElement, tail: BaseElement) -> BaseElement {
    let mut result = base;
    for _ in 0..N {
        result = result.square();
    }
    result * tail
}

// Returns a y with y < 2M and y = x mod M.
// Note that in general *not*: reduce_le_2m(reduce_le_2m(x)) == x
#[inline(always)]
const fn reduce_le_2m(x: u32) -> u32 {
    // Note 2²³ = 2²° - 1 mod M. So, writing  x = x₁ 2²³ + x₂ with x₂ < 2²³
    // and x₁ < 2³, we have x = y (mod M) where
    // y = x₂ + x₁ 2²° - x₁ ≤ 2²³ + 2²° < 2M.
    let x1 = x >> 23;
    let x2 = x & 0x7fffff; // 2²³-1
    x2 + (x1 << 20) - x1
}

/// Montgomery reduction (constant time)
///
/// For x R ≤ M 2³², finds y ≤ 2M with y = x mod M.
#[inline(always)]
const fn mont_red_cst(x: u64) -> u32 {
    // 0x6fffff = -(q⁻¹) mod 2³²
    let m = x.wrapping_mul(0x6fffff) & 0xffffffff;
    ((x + m * (M as u64)) >> 32) as u32
}
