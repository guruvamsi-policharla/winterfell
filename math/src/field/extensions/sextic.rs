// Copyright (c) 2022 Cloudflare, Inc. and contributors.
// Licensed under the BSD-3-Clause license found in the LICENSE file or
// at https://opensource.org/licenses/BSD-3-Clause

use super::cubic::CubeExtension;
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

// SEXTIC EXTENSION FIELD
// ================================================================================================

/// Represents an element of a sextic extension, it's implemented as a quadractic extension of
/// a cubic extension of a [StarkField](crate::StarkField).
///
/// The extension element is defined as α + β * φ, where φ is a root of in irreducible polynomial
/// defined by the implementation of the [ExtensibleField] trait, and α and β are cubic extension
/// field elements.
#[repr(C)]
#[derive(Copy, Clone, Debug, PartialEq, Eq, Default)]
pub struct SexticExtension<B: ExtensibleField<3> + ExtensibleField<6> + StarkField>(
    CubeExtension<B>,
    CubeExtension<B>,
);

impl<B: ExtensibleField<3> + ExtensibleField<6> + StarkField> SexticExtension<B> {
    /// Returns a new extension element instantiated from the provided base elements.
    pub fn new(a: CubeExtension<B>, b: CubeExtension<B>) -> Self {
        Self(a, b)
    }

    /// Returns true if the base field specified by B type parameter supports sextic extensions.
    pub fn is_supported() -> bool {
        <B as ExtensibleField<6>>::is_supported()
    }

    /// Converts a vector of cubic extension elements into a vector of elements in a sextic
    /// extension field by fusing two adjacent cubic extension elements together. The output
    /// vector is half the length of the source vector.
    fn base_to_sextic_vector(source: Vec<CubeExtension<B>>) -> Vec<Self> {
        debug_assert!(
            source.len() % 2 == 0,
            "source vector length must be divisible by two, but was {}",
            source.len()
        );
        let mut v = core::mem::ManuallyDrop::new(source);
        let p = v.as_mut_ptr();
        let len = v.len() / 2;
        let cap = v.capacity() / 2;
        unsafe { Vec::from_raw_parts(p as *mut Self, len, cap) }
    }
}

impl<B: ExtensibleField<3> + ExtensibleField<6> + StarkField> FieldElement for SexticExtension<B> {
    type PositiveInteger = B::PositiveInteger;
    type BaseField = B;

    const ELEMENT_BYTES: usize = 2 * <CubeExtension<B> as FieldElement>::ELEMENT_BYTES;
    const IS_CANONICAL: bool = <CubeExtension<B> as FieldElement>::IS_CANONICAL;
    const ZERO: Self = Self(CubeExtension::<B>::ZERO, CubeExtension::<B>::ZERO);
    const ONE: Self = Self(CubeExtension::<B>::ONE, CubeExtension::<B>::ZERO);

    #[inline]
    fn double(self) -> Self {
        Self(self.0.double(), self.1.double())
    }

    #[inline]
    fn inv(self) -> Self {
        if self == Self::ZERO {
            return self;
        }
        // inverse as in complex numbers, but norm is a^2 + 3b^2.
        let three: CubeExtension<B> = 3u32.into();
        let norm = (self.0 * self.0) + (three * self.1 * self.1);
        let den = norm.inv();
        Self(self.0 * den, (-self.1) * den)
    }

    #[inline]
    fn conjugate(&self) -> Self {
        let x = [self.0, self.1];
        let mut y: [B; 6] = Default::default();
        y.copy_from_slice(<CubeExtension<B> as FieldElement>::as_base_elements(&x));
        let r = <B as ExtensibleField<6>>::frobenius(y);
        Self(
            CubeExtension::new(r[0], r[1], r[2]),
            CubeExtension::new(r[3], r[4], r[5]),
        )
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
        // get twice the number of cubic extesnion elements, and re-interpret them as sextic
        // extension field elements.
        let result = CubeExtension::zeroed_vector(n * 2);
        Self::base_to_sextic_vector(result)
    }

    fn as_base_elements(elements: &[Self]) -> &[Self::BaseField] {
        let ptr = elements.as_ptr();
        let len = elements.len() * 2 * 3;
        unsafe { slice::from_raw_parts(ptr as *const Self::BaseField, len) }
    }
}

impl<B: ExtensibleField<3> + ExtensibleField<6> + StarkField> ExtensionOf<CubeExtension<B>>
    for SexticExtension<B>
{
    #[inline(always)]
    fn mul_base(self, other: CubeExtension<B>) -> Self {
        Self(self.0 * other, self.1 * other)
    }
}

impl<B: ExtensibleField<3> + ExtensibleField<6> + StarkField> ExtensionOf<B>
    for SexticExtension<B>
{
    #[inline(always)]
    fn mul_base(self, other: B) -> Self {
        let x = [self.0, self.1];
        let mut y: [B; 6] = Default::default();
        y.copy_from_slice(<CubeExtension<B> as FieldElement>::as_base_elements(&x));
        let r = <B as ExtensibleField<6>>::mul_base(y, other);
        Self(
            CubeExtension::new(r[0], r[1], r[2]),
            CubeExtension::new(r[3], r[4], r[5]),
        )
    }
}

impl<B: ExtensibleField<3> + ExtensibleField<6> + StarkField> Randomizable for SexticExtension<B> {
    const VALUE_SIZE: usize = Self::ELEMENT_BYTES;

    fn from_random_bytes(source: &[u8]) -> Option<Self> {
        if source.len() >= Self::VALUE_SIZE {
            let n = <CubeExtension<B> as Randomizable>::VALUE_SIZE;
            let frb = <CubeExtension<B> as Randomizable>::from_random_bytes;
            if let Some(x0) = frb(&source[0..n]) {
                if let Some(x1) = frb(&source[n..2 * n]) {
                    return Some(Self(x0, x1));
                }
            }
        }
        None
    }
}

impl<B: ExtensibleField<3> + ExtensibleField<6> + StarkField> fmt::Display for SexticExtension<B> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "({}, {})", self.0, self.1)
    }
}

// OVERLOADED OPERATORS
// ------------------------------------------------------------------------------------------------

impl<B: ExtensibleField<3> + ExtensibleField<6> + StarkField> Add for SexticExtension<B> {
    type Output = Self;

    #[inline]
    fn add(self, rhs: Self) -> Self {
        Self(self.0 + rhs.0, self.1 + rhs.1)
    }
}

impl<B: ExtensibleField<3> + ExtensibleField<6> + StarkField> AddAssign for SexticExtension<B> {
    #[inline]
    fn add_assign(&mut self, rhs: Self) {
        *self = *self + rhs
    }
}

impl<B: ExtensibleField<3> + ExtensibleField<6> + StarkField> Sub for SexticExtension<B> {
    type Output = Self;

    #[inline]
    fn sub(self, rhs: Self) -> Self {
        Self(self.0 - rhs.0, self.1 - rhs.1)
    }
}

impl<B: ExtensibleField<3> + ExtensibleField<6> + StarkField> SubAssign for SexticExtension<B> {
    #[inline]
    fn sub_assign(&mut self, rhs: Self) {
        *self = *self - rhs;
    }
}

impl<B: ExtensibleField<3> + ExtensibleField<6> + StarkField> Mul for SexticExtension<B> {
    type Output = Self;

    #[inline]
    fn mul(self, rhs: Self) -> Self {
        let x0 = [self.0, self.1];
        let mut y0: [B; 6] = Default::default();
        y0.copy_from_slice(<CubeExtension<B> as FieldElement>::as_base_elements(&x0));

        let x1 = [rhs.0, rhs.1];
        let mut y1: [B; 6] = Default::default();
        y1.copy_from_slice(<CubeExtension<B> as FieldElement>::as_base_elements(&x1));

        let r = <B as ExtensibleField<6>>::mul(y0, y1);
        Self(
            CubeExtension::new(r[0], r[1], r[2]),
            CubeExtension::new(r[3], r[4], r[5]),
        )
    }
}

impl<B: ExtensibleField<3> + ExtensibleField<6> + StarkField> MulAssign for SexticExtension<B> {
    #[inline]
    fn mul_assign(&mut self, rhs: Self) {
        *self = *self * rhs
    }
}

impl<B: ExtensibleField<3> + ExtensibleField<6> + StarkField> Div for SexticExtension<B> {
    type Output = Self;

    #[inline]
    #[allow(clippy::suspicious_arithmetic_impl)]
    fn div(self, rhs: Self) -> Self {
        self * rhs.inv()
    }
}

impl<B: ExtensibleField<3> + ExtensibleField<6> + StarkField> DivAssign for SexticExtension<B> {
    #[inline]
    fn div_assign(&mut self, rhs: Self) {
        *self = *self / rhs
    }
}

impl<B: ExtensibleField<3> + ExtensibleField<6> + StarkField> Neg for SexticExtension<B> {
    type Output = Self;

    #[inline]
    fn neg(self) -> Self {
        Self(-self.0, -self.1)
    }
}

// TYPE CONVERSIONS
// ------------------------------------------------------------------------------------------------

impl<B: ExtensibleField<3> + ExtensibleField<6> + StarkField> From<CubeExtension<B>>
    for SexticExtension<B>
{
    fn from(value: CubeExtension<B>) -> Self {
        Self(value, CubeExtension::ZERO)
    }
}

impl<B: ExtensibleField<3> + ExtensibleField<6> + StarkField> From<B> for SexticExtension<B> {
    fn from(value: B) -> Self {
        Self(CubeExtension::from(value), CubeExtension::ZERO)
    }
}

impl<B: ExtensibleField<3> + ExtensibleField<6> + StarkField> From<u128> for SexticExtension<B> {
    fn from(value: u128) -> Self {
        Self(CubeExtension::from(value), CubeExtension::ZERO)
    }
}

impl<B: ExtensibleField<3> + ExtensibleField<6> + StarkField> From<u64> for SexticExtension<B> {
    fn from(value: u64) -> Self {
        Self(CubeExtension::from(value), CubeExtension::ZERO)
    }
}

impl<B: ExtensibleField<3> + ExtensibleField<6> + StarkField> From<u32> for SexticExtension<B> {
    fn from(value: u32) -> Self {
        Self(CubeExtension::from(value), CubeExtension::ZERO)
    }
}

impl<B: ExtensibleField<3> + ExtensibleField<6> + StarkField> From<u16> for SexticExtension<B> {
    fn from(value: u16) -> Self {
        Self(CubeExtension::from(value), CubeExtension::ZERO)
    }
}

impl<B: ExtensibleField<3> + ExtensibleField<6> + StarkField> From<u8> for SexticExtension<B> {
    fn from(value: u8) -> Self {
        Self(CubeExtension::from(value), CubeExtension::ZERO)
    }
}
impl<'a, B: ExtensibleField<3> + ExtensibleField<6> + StarkField> TryFrom<&'a [u8]>
    for SexticExtension<B>
{
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

impl<B: ExtensibleField<3> + ExtensibleField<6> + StarkField> AsBytes for SexticExtension<B> {
    fn as_bytes(&self) -> &[u8] {
        // TODO: take endianness into account
        let self_ptr: *const Self = self;
        unsafe { slice::from_raw_parts(self_ptr as *const u8, Self::ELEMENT_BYTES) }
    }
}

// SERIALIZATION / DESERIALIZATION
// ------------------------------------------------------------------------------------------------

impl<B: ExtensibleField<3> + ExtensibleField<6> + StarkField> Serializable for SexticExtension<B> {
    fn write_into<W: ByteWriter>(&self, target: &mut W) {
        self.0.write_into(target);
        self.1.write_into(target);
    }
}

impl<B: ExtensibleField<3> + ExtensibleField<6> + StarkField> Deserializable
    for SexticExtension<B>
{
    fn read_from<R: ByteReader>(source: &mut R) -> Result<Self, DeserializationError> {
        let value0 = CubeExtension::read_from(source)?;
        let value1 = CubeExtension::read_from(source)?;
        Ok(Self(value0, value1))
    }
}

// TESTS
// ================================================================================================

#[cfg(test)]
mod tests {
    use super::{CubeExtension, DeserializationError, FieldElement, SexticExtension};
    use crate::field::f23201::BaseElement;
    use rand_utils::rand_value;
    use utils::AsBytes;

    // BASIC ALGEBRA
    // --------------------------------------------------------------------------------------------

    #[test]
    fn add() {
        // identity
        let r: SexticExtension<BaseElement> = rand_value();
        assert_eq!(r, r + SexticExtension::<BaseElement>::ZERO);

        // test random values
        let r1: SexticExtension<BaseElement> = rand_value();
        let r2: SexticExtension<BaseElement> = rand_value();

        let expected = SexticExtension(r1.0 + r2.0, r1.1 + r2.1);
        assert_eq!(expected, r1 + r2);
    }

    #[test]
    fn sub() {
        // identity
        let r: SexticExtension<BaseElement> = rand_value();
        assert_eq!(r, r - SexticExtension::<BaseElement>::ZERO);

        // test random values
        let r1: SexticExtension<BaseElement> = rand_value();
        let r2: SexticExtension<BaseElement> = rand_value();

        let expected = SexticExtension(r1.0 - r2.0, r1.1 - r2.1);
        assert_eq!(expected, r1 - r2);
    }

    #[test]
    fn div() {
        // div by zero
        let z = SexticExtension::<BaseElement>::ZERO;
        assert_eq!(z, z.inv());

        // one div one
        let i = SexticExtension::<BaseElement>::ONE;
        assert_eq!(SexticExtension::<BaseElement>::ONE, i / 1u32.into());

        // test div
        let r1: SexticExtension<BaseElement> = rand_value();
        let r2: SexticExtension<BaseElement> = rand_value();

        let expected = r1 * (r2.inv());
        assert_eq!(expected, r1 / r2);

        // test inverse
        let r3: SexticExtension<BaseElement> = rand_value();
        assert_eq!(SexticExtension::<BaseElement>::ONE, r3 / r3);
    }

    // INITIALIZATION
    // --------------------------------------------------------------------------------------------

    #[test]
    fn zeroed_vector() {
        let result = SexticExtension::<BaseElement>::zeroed_vector(6);
        assert_eq!(6, result.len());
        for element in result.into_iter() {
            assert_eq!(SexticExtension::<BaseElement>::ZERO, element);
        }
    }

    // SERIALIZATION / DESERIALIZATION
    // --------------------------------------------------------------------------------------------

    #[test]
    fn elements_as_bytes() {
        let source = vec![
            SexticExtension(
                CubeExtension::new(
                    BaseElement::new(11).into(),
                    BaseElement::new(12).into(),
                    BaseElement::new(13).into(),
                ),
                CubeExtension::new(
                    BaseElement::new(25).into(),
                    BaseElement::new(26).into(),
                    BaseElement::new(27).into(),
                ),
            ),
            SexticExtension(
                CubeExtension::new(
                    BaseElement::new(34).into(),
                    BaseElement::new(35).into(),
                    BaseElement::new(36).into(),
                ),
                CubeExtension::new(
                    BaseElement::new(47).into(),
                    BaseElement::new(48).into(),
                    BaseElement::new(49).into(),
                ),
            ),
        ];

        let mut expected = vec![];
        expected.extend_from_slice(&source[0].as_bytes());
        expected.extend_from_slice(&source[1].as_bytes());

        assert_eq!(
            expected,
            SexticExtension::<BaseElement>::elements_as_bytes(&source)
        );
    }

    #[test]
    fn bytes_as_elements() {
        let elements = vec![
            SexticExtension(
                CubeExtension::new(
                    BaseElement::new(11).into(),
                    BaseElement::new(12).into(),
                    BaseElement::new(13).into(),
                ),
                CubeExtension::new(
                    BaseElement::new(25).into(),
                    BaseElement::new(26).into(),
                    BaseElement::new(27).into(),
                ),
            ),
            SexticExtension(
                CubeExtension::new(
                    BaseElement::new(34).into(),
                    BaseElement::new(35).into(),
                    BaseElement::new(36).into(),
                ),
                CubeExtension::new(
                    BaseElement::new(47).into(),
                    BaseElement::new(48).into(),
                    BaseElement::new(49).into(),
                ),
            ),
        ];

        let mut bytes = vec![];
        bytes.extend_from_slice(&elements[0].as_bytes());
        bytes.extend_from_slice(&elements[1].as_bytes());
        bytes.extend_from_slice(&BaseElement::new(77).inner().to_le_bytes());
        let result = unsafe {
            SexticExtension::<BaseElement>::bytes_as_elements(
                &bytes[..2 * SexticExtension::<BaseElement>::ELEMENT_BYTES],
            )
        };
        assert!(result.is_ok());
        assert_eq!(elements, result.unwrap());

        let result = unsafe { SexticExtension::<BaseElement>::bytes_as_elements(&bytes) };
        assert!(matches!(result, Err(DeserializationError::InvalidValue(_))));

        let result = unsafe { SexticExtension::<BaseElement>::bytes_as_elements(&bytes[1..]) };
        assert!(matches!(result, Err(DeserializationError::InvalidValue(_))));
    }

    // UTILITIES
    // --------------------------------------------------------------------------------------------

    #[test]
    fn as_base_elements() {
        let elements = vec![
            SexticExtension(
                CubeExtension::new(
                    BaseElement::new(11).into(),
                    BaseElement::new(12).into(),
                    BaseElement::new(13).into(),
                ),
                CubeExtension::new(
                    BaseElement::new(25).into(),
                    BaseElement::new(26).into(),
                    BaseElement::new(27).into(),
                ),
            ),
            SexticExtension(
                CubeExtension::new(
                    BaseElement::new(34).into(),
                    BaseElement::new(35).into(),
                    BaseElement::new(36).into(),
                ),
                CubeExtension::new(
                    BaseElement::new(47).into(),
                    BaseElement::new(48).into(),
                    BaseElement::new(49).into(),
                ),
            ),
        ];

        let expected = vec![
            BaseElement::new(11),
            BaseElement::new(12),
            BaseElement::new(13),
            BaseElement::new(25),
            BaseElement::new(26),
            BaseElement::new(27),
            BaseElement::new(34),
            BaseElement::new(35),
            BaseElement::new(36),
            BaseElement::new(47),
            BaseElement::new(48),
            BaseElement::new(49),
        ];

        assert_eq!(
            expected,
            SexticExtension::<BaseElement>::as_base_elements(&elements)
        );
    }
}
