// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.

use super::{ExtensibleField, ExtensionOf, FieldElement};
use crate::StarkField;
use core::{
    convert::TryFrom,
    fmt,
    ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Neg, Sub, SubAssign},
    slice,
};
use utils::{
    collections::Vec, string::ToString, AsBytes, ByteReader, ByteWriter, Deserializable,
    DeserializationError, Randomizable, Serializable, SliceReader,
};

// QUADRATIC EXTENSION FIELD
// ================================================================================================

/// Represents an element in a cubic extension of a [StarkField](crate::StarkField).
///
/// The extension element is defined as α + β * φ + γ * φ^2, where φ is a root of in irreducible
/// polynomial defined by the implementation of the [ExtensibleField] trait, and α, β, γ are base
/// field elements.
#[repr(C)]
#[derive(Copy, Clone, Debug, PartialEq, Eq, Default)]
pub struct CubeExtension<B: ExtensibleField<3> + StarkField>(B, B, B);

impl<B: ExtensibleField<3> + StarkField> CubeExtension<B> {
    /// Returns a new extension element instantiated from the provided base elements.
    pub fn new(a: B, b: B, c: B) -> Self {
        Self(a, b, c)
    }

    /// Returns true if the base field specified by B type parameter supports cubic extensions.
    pub fn is_supported() -> bool {
        <B as ExtensibleField<3>>::is_supported()
    }

    /// Converts a vector of base elements into a vector of elements in a cubic extension field
    /// by fusing three adjacent base elements together. The output vector is half the length of
    /// the source vector.
    fn base_to_cubic_vector(source: Vec<B>) -> Vec<Self> {
        debug_assert!(
            source.len() % 3 == 0,
            "source vector length must be divisible by three, but was {}",
            source.len()
        );
        let mut v = core::mem::ManuallyDrop::new(source);
        let p = v.as_mut_ptr();
        let len = v.len() / 3;
        let cap = v.capacity() / 3;
        unsafe { Vec::from_raw_parts(p as *mut Self, len, cap) }
    }
}

impl<B: ExtensibleField<3> + StarkField> FieldElement for CubeExtension<B> {
    type PositiveInteger = B::PositiveInteger;
    type BaseField = B;

    const ELEMENT_BYTES: usize = B::ELEMENT_BYTES * 3;
    const IS_CANONICAL: bool = B::IS_CANONICAL;
    const ZERO: Self = Self(B::ZERO, B::ZERO, B::ZERO);
    const ONE: Self = Self(B::ONE, B::ZERO, B::ZERO);

    #[inline]
    fn double(self) -> Self {
        Self(self.0.double(), self.1.double(), self.2.double())
    }

    #[inline]
    fn inv(self) -> Self {
        if self == Self::ZERO {
            return self;
        }

        let x = [self.0, self.1, self.2];
        let c1 = <B as ExtensibleField<3>>::frobenius(x);
        let c2 = <B as ExtensibleField<3>>::frobenius(c1);
        let numerator = <B as ExtensibleField<3>>::mul(c1, c2);

        let norm = <B as ExtensibleField<3>>::mul(x, numerator);
        debug_assert_eq!(norm[1], B::ZERO, "norm must be in the base field");
        debug_assert_eq!(norm[2], B::ZERO, "norm must be in the base field");
        let denom_inv = norm[0].inv();

        Self(
            numerator[0] * denom_inv,
            numerator[1] * denom_inv,
            numerator[2] * denom_inv,
        )
    }

    #[inline]
    fn conjugate(&self) -> Self {
        let result = <B as ExtensibleField<3>>::frobenius([self.0, self.1, self.2]);
        Self(result[0], result[1], result[2])
    }

    fn elements_as_bytes(elements: &[Self]) -> &[u8] {
        unsafe {
            slice::from_raw_parts(
                elements.as_ptr() as *const u8,
                elements.len() * Self::ELEMENT_BYTES,
            )
        }
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

        // make sure the bytes are aligned on the boundary consistent with base element alignment
        if (p as usize) % Self::BaseField::ELEMENT_BYTES != 0 {
            return Err(DeserializationError::InvalidValue(
                "slice memory alignment is not valid for this field element type".to_string(),
            ));
        }

        Ok(slice::from_raw_parts(p as *const Self, len))
    }

    fn zeroed_vector(n: usize) -> Vec<Self> {
        // get three times the number of base elements and re-interpret them as cubic field
        // elements
        let result = B::zeroed_vector(n * 3);
        Self::base_to_cubic_vector(result)
    }

    fn as_base_elements(elements: &[Self]) -> &[Self::BaseField] {
        let ptr = elements.as_ptr();
        let len = elements.len() * 3;
        unsafe { slice::from_raw_parts(ptr as *const Self::BaseField, len) }
    }
}

impl<B: ExtensibleField<3> + StarkField> ExtensionOf<B> for CubeExtension<B> {
    #[inline(always)]
    fn mul_base(self, other: B) -> Self {
        let result = <B as ExtensibleField<3>>::mul_base([self.0, self.1, self.2], other);
        Self(result[0], result[1], result[2])
    }
}

impl<B: ExtensibleField<3> + StarkField> Randomizable for CubeExtension<B> {
    const VALUE_SIZE: usize = Self::ELEMENT_BYTES;

    fn from_random_bytes(bytes: &[u8]) -> Option<Self> {
        Self::try_from(bytes).ok()
    }
}

impl<B: ExtensibleField<3> + StarkField> fmt::Display for CubeExtension<B> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "({}, {}, {})", self.0, self.1, self.2)
    }
}

// OVERLOADED OPERATORS
// ------------------------------------------------------------------------------------------------

impl<B: ExtensibleField<3> + StarkField> Add for CubeExtension<B> {
    type Output = Self;

    #[inline]
    fn add(self, rhs: Self) -> Self {
        Self(self.0 + rhs.0, self.1 + rhs.1, self.2 + rhs.2)
    }
}

impl<B: ExtensibleField<3> + StarkField> AddAssign for CubeExtension<B> {
    #[inline]
    fn add_assign(&mut self, rhs: Self) {
        *self = *self + rhs
    }
}

impl<B: ExtensibleField<3> + StarkField> Sub for CubeExtension<B> {
    type Output = Self;

    #[inline]
    fn sub(self, rhs: Self) -> Self {
        Self(self.0 - rhs.0, self.1 - rhs.1, self.2 - rhs.2)
    }
}

impl<B: ExtensibleField<3> + StarkField> SubAssign for CubeExtension<B> {
    #[inline]
    fn sub_assign(&mut self, rhs: Self) {
        *self = *self - rhs;
    }
}

impl<B: ExtensibleField<3> + StarkField> Mul for CubeExtension<B> {
    type Output = Self;

    #[inline]
    fn mul(self, rhs: Self) -> Self {
        let result =
            <B as ExtensibleField<3>>::mul([self.0, self.1, self.2], [rhs.0, rhs.1, rhs.2]);
        Self(result[0], result[1], result[2])
    }
}

impl<B: ExtensibleField<3> + StarkField> MulAssign for CubeExtension<B> {
    #[inline]
    fn mul_assign(&mut self, rhs: Self) {
        *self = *self * rhs
    }
}

impl<B: ExtensibleField<3> + StarkField> Div for CubeExtension<B> {
    type Output = Self;

    #[inline]
    #[allow(clippy::suspicious_arithmetic_impl)]
    fn div(self, rhs: Self) -> Self {
        self * rhs.inv()
    }
}

impl<B: ExtensibleField<3> + StarkField> DivAssign for CubeExtension<B> {
    #[inline]
    fn div_assign(&mut self, rhs: Self) {
        *self = *self / rhs
    }
}

impl<B: ExtensibleField<3> + StarkField> Neg for CubeExtension<B> {
    type Output = Self;

    #[inline]
    fn neg(self) -> Self {
        Self(-self.0, -self.1, -self.2)
    }
}

// TYPE CONVERSIONS
// ------------------------------------------------------------------------------------------------

impl<B: ExtensibleField<3> + StarkField> From<B> for CubeExtension<B> {
    fn from(value: B) -> Self {
        Self(value, B::ZERO, B::ZERO)
    }
}

impl<B: ExtensibleField<3> + StarkField> From<u128> for CubeExtension<B> {
    fn from(value: u128) -> Self {
        Self(B::from(value), B::ZERO, B::ZERO)
    }
}

impl<B: ExtensibleField<3> + StarkField> From<u64> for CubeExtension<B> {
    fn from(value: u64) -> Self {
        Self(B::from(value), B::ZERO, B::ZERO)
    }
}

impl<B: ExtensibleField<3> + StarkField> From<u32> for CubeExtension<B> {
    fn from(value: u32) -> Self {
        Self(B::from(value), B::ZERO, B::ZERO)
    }
}

impl<B: ExtensibleField<3> + StarkField> From<u16> for CubeExtension<B> {
    fn from(value: u16) -> Self {
        Self(B::from(value), B::ZERO, B::ZERO)
    }
}

impl<B: ExtensibleField<3> + StarkField> From<u8> for CubeExtension<B> {
    fn from(value: u8) -> Self {
        Self(B::from(value), B::ZERO, B::ZERO)
    }
}

impl<'a, B: ExtensibleField<3> + StarkField> TryFrom<&'a [u8]> for CubeExtension<B> {
    type Error = DeserializationError;

    /// Converts a slice of bytes into a field element; returns error if the value encoded in bytes
    /// is not a valid field element. The bytes are assumed to be in little-endian byte order.
    fn try_from(bytes: &[u8]) -> Result<Self, Self::Error> {
        if bytes.len() < Self::ELEMENT_BYTES {
            return Err(DeserializationError::InvalidValue(format!(
                "not enough bytes for a full field element; expected {} bytes, but was {} bytes",
                Self::ELEMENT_BYTES,
                bytes.len(),
            )));
        }
        if bytes.len() > Self::ELEMENT_BYTES {
            return Err(DeserializationError::InvalidValue(format!(
                "too many bytes for a field element; expected {} bytes, but was {} bytes",
                Self::ELEMENT_BYTES,
                bytes.len(),
            )));
        }
        let mut reader = SliceReader::new(bytes);
        Self::read_from(&mut reader)
    }
}

impl<B: ExtensibleField<3> + StarkField> AsBytes for CubeExtension<B> {
    fn as_bytes(&self) -> &[u8] {
        // TODO: take endianness into account
        let self_ptr: *const Self = self;
        unsafe { slice::from_raw_parts(self_ptr as *const u8, Self::ELEMENT_BYTES) }
    }
}

// SERIALIZATION / DESERIALIZATION
// ------------------------------------------------------------------------------------------------

impl<B: ExtensibleField<3> + StarkField> Serializable for CubeExtension<B> {
    fn write_into<W: ByteWriter>(&self, target: &mut W) {
        self.0.write_into(target);
        self.1.write_into(target);
        self.2.write_into(target);
    }
}

impl<B: ExtensibleField<3> + StarkField> Deserializable for CubeExtension<B> {
    fn read_from<R: ByteReader>(source: &mut R) -> Result<Self, DeserializationError> {
        let value0 = B::read_from(source)?;
        let value1 = B::read_from(source)?;
        let value2 = B::read_from(source)?;
        Ok(Self(value0, value1, value2))
    }
}

// QUADRATIC EXTENSION TO BUILD A SEXTIC EXTENSION
// ================================================================================================

/// Defines a quadratic extension of the cubic extension field using an irreducible polynomial x² + 3.
/// Thus, a sextic extension element is defined as α + β * φ, where φ is a root of this polynomial,
/// and α and β are cubic extension field elements.

// Implementing the extension Fp^6 as Fp^3[x] / (x^2 + 3).
impl<B: ExtensibleField<3> + StarkField> ExtensibleField<2> for CubeExtension<B>
where
    Self: FieldElement<BaseField = B>,
{
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
        // multiplying an extension field element by a base field element requires just 2
        // multiplications in the cubic extension field.
        [a[0] * b, a[1] * b]
    }

    #[inline(always)]
    fn frobenius(x: [Self; 2]) -> [Self; 2] {
        // given x = α + β * φ
        // frobenius(x) = frobenius(α) + frobenius(β) * frobenius(φ)
        //              = frobenius(α) - frobenius(β) * φ
        let a = <B as ExtensibleField<3>>::frobenius([x[0].0, x[0].1, x[0].2]);
        let b = <B as ExtensibleField<3>>::frobenius([x[1].0, x[1].1, x[1].2]);
        [
            CubeExtension::<B>::new(a[0], a[1], a[2]),
            -CubeExtension::<B>::new(b[0], b[1], b[2]),
        ]
    }
}

// TESTS
// ================================================================================================

#[cfg(test)]
mod tests {
    use super::{CubeExtension, DeserializationError, FieldElement};
    use crate::field::f64::BaseElement;
    use rand_utils::rand_value;

    // BASIC ALGEBRA
    // --------------------------------------------------------------------------------------------

    #[test]
    fn add() {
        // identity
        let r: CubeExtension<BaseElement> = rand_value();
        assert_eq!(r, r + CubeExtension::<BaseElement>::ZERO);

        // test random values
        let r1: CubeExtension<BaseElement> = rand_value();
        let r2: CubeExtension<BaseElement> = rand_value();

        let expected = CubeExtension(r1.0 + r2.0, r1.1 + r2.1, r1.2 + r2.2);
        assert_eq!(expected, r1 + r2);
    }

    #[test]
    fn sub() {
        // identity
        let r: CubeExtension<BaseElement> = rand_value();
        assert_eq!(r, r - CubeExtension::<BaseElement>::ZERO);

        // test random values
        let r1: CubeExtension<BaseElement> = rand_value();
        let r2: CubeExtension<BaseElement> = rand_value();

        let expected = CubeExtension(r1.0 - r2.0, r1.1 - r2.1, r1.2 - r2.2);
        assert_eq!(expected, r1 - r2);
    }

    // INITIALIZATION
    // --------------------------------------------------------------------------------------------

    #[test]
    fn zeroed_vector() {
        let result = CubeExtension::<BaseElement>::zeroed_vector(4);
        assert_eq!(4, result.len());
        for element in result.into_iter() {
            assert_eq!(CubeExtension::<BaseElement>::ZERO, element);
        }
    }

    // SERIALIZATION / DESERIALIZATION
    // --------------------------------------------------------------------------------------------

    #[test]
    fn elements_as_bytes() {
        let source = vec![
            CubeExtension(
                BaseElement::new(1),
                BaseElement::new(2),
                BaseElement::new(3),
            ),
            CubeExtension(
                BaseElement::new(4),
                BaseElement::new(5),
                BaseElement::new(6),
            ),
        ];

        let mut expected = vec![];
        expected.extend_from_slice(&source[0].0.inner().to_le_bytes());
        expected.extend_from_slice(&source[0].1.inner().to_le_bytes());
        expected.extend_from_slice(&source[0].2.inner().to_le_bytes());
        expected.extend_from_slice(&source[1].0.inner().to_le_bytes());
        expected.extend_from_slice(&source[1].1.inner().to_le_bytes());
        expected.extend_from_slice(&source[1].2.inner().to_le_bytes());

        assert_eq!(
            expected,
            CubeExtension::<BaseElement>::elements_as_bytes(&source)
        );
    }

    #[test]
    fn bytes_as_elements() {
        let elements = vec![
            CubeExtension(
                BaseElement::new(1),
                BaseElement::new(2),
                BaseElement::new(3),
            ),
            CubeExtension(
                BaseElement::new(4),
                BaseElement::new(5),
                BaseElement::new(6),
            ),
        ];

        let mut bytes = vec![];
        bytes.extend_from_slice(&elements[0].0.inner().to_le_bytes());
        bytes.extend_from_slice(&elements[0].1.inner().to_le_bytes());
        bytes.extend_from_slice(&elements[0].2.inner().to_le_bytes());
        bytes.extend_from_slice(&elements[1].0.inner().to_le_bytes());
        bytes.extend_from_slice(&elements[1].1.inner().to_le_bytes());
        bytes.extend_from_slice(&elements[1].2.inner().to_le_bytes());
        bytes.extend_from_slice(&BaseElement::new(5).inner().to_le_bytes());

        let result = unsafe { CubeExtension::<BaseElement>::bytes_as_elements(&bytes[..48]) };
        assert!(result.is_ok());
        assert_eq!(elements, result.unwrap());

        let result = unsafe { CubeExtension::<BaseElement>::bytes_as_elements(&bytes) };
        assert!(matches!(result, Err(DeserializationError::InvalidValue(_))));

        let result = unsafe { CubeExtension::<BaseElement>::bytes_as_elements(&bytes[1..]) };
        assert!(matches!(result, Err(DeserializationError::InvalidValue(_))));
    }

    // UTILITIES
    // --------------------------------------------------------------------------------------------

    #[test]
    fn as_base_elements() {
        let elements = vec![
            CubeExtension(
                BaseElement::new(1),
                BaseElement::new(2),
                BaseElement::new(3),
            ),
            CubeExtension(
                BaseElement::new(4),
                BaseElement::new(5),
                BaseElement::new(6),
            ),
        ];

        let expected = vec![
            BaseElement::new(1),
            BaseElement::new(2),
            BaseElement::new(3),
            BaseElement::new(4),
            BaseElement::new(5),
            BaseElement::new(6),
        ];

        assert_eq!(
            expected,
            CubeExtension::<BaseElement>::as_base_elements(&elements)
        );
    }
}
