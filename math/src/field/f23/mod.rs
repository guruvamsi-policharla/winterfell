//! An implementation of a 23-bit prime field with modulus $2^{23} - 2^{13} + 1$
//! used in CRYSTALS-Dilithium.


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
use core::{
    convert::{TryFrom},
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

/// Field modulus = 2^23 - 2^13 + 1
const M: u32 = 0x7fe001;

/// R^2 mod M; this is used for conversion of elements into Montgomery representation.
const R2: u32 = 0x2419ff;

/// 2^13 primitive root of unity
const G: u32 = 1938117;

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
        // M-2 = 11111111101111111111111; 9 ones followed by 13 ones.
        let t10 = self.square();
        let t11 = t10 * self;
        let t1100 = t11.square().square();
        let t1111 = t11 * t1100;
        let t11110 = t1111.square();
        let t11111 = t11110 * self;
        let t1x9 = exp_acc::<4>(t11110, t11111);
        let t1x901x9 = exp_acc::<10>(t1x9, t1x9);
        exp_acc::<4>(t1x901x9, t1111)
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
    const GENERATOR: Self = Self::new(10);
    const TWO_ADICITY: u32 = 13;
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

    fn from_random_bytes(bytes: &[u8]) -> Option<Self> {
        Self::try_from(bytes).ok()
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
        return self.as_int() == other.as_int()
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
        Self(reduce_le_2m(self.0 + 2*M - rhs.0))
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

/// Defines a quadratic extension of the base field over an irreducible polynomial x² - t - 1.
/// Thus, an extension element is defined as α + β * φ, where φ is a root of this polynomial,
/// and α and β are base field elements.
impl ExtensibleField<2> for BaseElement {
    #[inline(always)]
    fn mul(a: [Self; 2], b: [Self; 2]) -> [Self; 2] {
        let a0b0 = a[0] * b[0];
        [
            a0b0 + a[1] * b[1],
            (a[0] + a[1]) * (b[0] + b[1]) - a0b0,
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
        [x[0] + x[1], -x[1]]
    }
}

// CUBIC EXTENSION
// ================================================================================================

/// Defines a cubic extension of the base field over an irreducible polynomial x³ - 2.
/// Thus, an extension element is defined as α + β * φ + γ * φ², where φ is a root of this
/// polynomial, and α, β and γ are base field elements.
impl ExtensibleField<3> for BaseElement {
    #[inline(always)]
    fn mul(a: [Self; 3], b: [Self; 3]) -> [Self; 3] {
        // TODO We can reduce number of multiplications
        [
            a[0] * b[0] + (a[1] * b[2] + a[2] * b[1]).double(),
            a[0] * b[1] + a[1] * b[0] + (a[2] * b[2]).double(),
            a[0] * b[2] + a[1] * b[1] + a[2] * b[0]
        ]
    }

    #[inline(always)]
    fn mul_base(a: [Self; 3], b: Self) -> [Self; 3] {
        [a[0] * b, a[1] * b, a[2] * b]
    }

    #[inline(always)]
    fn frobenius(x: [Self; 3]) -> [Self; 3] {
        [
            x[0],
            Self::new(949247) * x[1],
            Self::new(7431169) * x[2],
        ]
    }
}

// TYPE CONVERSIONS
// ================================================================================================

impl From<u128> for BaseElement {
    fn from(x: u128) -> Self {
        // TODO optimize
        Self::new(x as u32)
            + Self::new((x >> 32) as u32) * Self::new(0x3ffe00)
            + Self::new((x >> 64) as u32) * Self::new(0x2419ff)
            + Self::new((x >> 96) as u32) * Self::new(0x18510d)
    }
}

impl From<u64> for BaseElement {
    fn from(value: u64) -> Self {
        // TODO optimize
        Self::new(value as u32) + Self::new((value >> 32) as u32) * Self::new(0x3ffe00)
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

        let value = (bytes[0] as u32) + ((bytes[1] as u32) << 8) + (((bytes[2] & 127) as u32) << 16);
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
        let x = self.as_int();
        target.write_u8(x as u8);
        target.write_u8((x >> 8) as u8);
        target.write_u8((x >> 16) as u8);
    }
}

impl Deserializable for BaseElement {
    fn read_from<R: ByteReader>(source: &mut R) -> Result<Self, DeserializationError> {
        // TODO we ignore the most significant bit. Is that ok?
        let x0 = source.read_u8()?;
        let x1 = source.read_u8()?;
        let x2 = source.read_u8()?;
        let value = (x0 as u32) + ((x1 as u32) << 8) + (((x2 & 127) as u32) << 16);
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
const fn reduce_le_2m(x : u32) -> u32 {
    // Note 2²³ = 2¹³ - 1 mod M. So, writing  x = x₁ 2²³ + x₂ with x₂ < 2²³
    // and x₁ < 2⁹, we have x = y (mod M) where
    // y = x₂ + x₁ 2¹³ - x₁ ≤ 2²³ + 2¹³ < 2M.
    let x1 = x >> 23;
    let x2 = x & 0x7fffff; // 2²³-1
    x2 + (x1 << 13) - x1
}

/// Montgomery reduction (constant time)
///
/// For x R ≤ M 2³², finds y ≤ 2M with y = x mod M.
#[inline(always)]
const fn mont_red_cst(x: u64) -> u32 {
    // 4236238847 = -(q⁻¹) mod 2³²
    let m = x.wrapping_mul(4236238847) & 0xffffffff;
    ((x + m*(M as u64)) >> 32) as u32
}
