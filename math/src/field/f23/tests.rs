// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.

use super::{BaseElement, DeserializationError, FieldElement, Serializable, StarkField, M};
use crate::field::{CubeExtension, ExtensionOf, QuadExtension};
use core::convert::TryFrom;
use num_bigint::BigUint;
use proptest::prelude::*;
use rand_utils::rand_value;

// MANUAL TESTS
// ================================================================================================

#[test]
fn add() {
    // identity
    let r: BaseElement = rand_value();
    assert_eq!(r, r + BaseElement::ZERO);

    // test addition within bounds
    assert_eq!(
        BaseElement::new(5),
        BaseElement::new(2) + BaseElement::new(3)
    );

    // test overflow
    let t = BaseElement::new(M - 1);
    assert_eq!(BaseElement::ZERO, t + BaseElement::ONE);
    assert_eq!(BaseElement::ONE, t + BaseElement::new(2));
}

#[test]
fn sub() {
    // identity
    let r: BaseElement = rand_value();
    assert_eq!(r, r - BaseElement::ZERO);

    // test subtraction within bounds
    assert_eq!(
        BaseElement::new(2),
        BaseElement::new(5) - BaseElement::new(3)
    );

    // test underflow
    let expected = BaseElement::new(M - 2);
    assert_eq!(expected, BaseElement::new(3) - BaseElement::new(5));
}

#[test]
fn neg() {
    assert_eq!(BaseElement::ZERO, -BaseElement::ZERO);
    assert_eq!(BaseElement::from(super::M - 1), -BaseElement::ONE);

    let r: BaseElement = rand_value();
    assert_eq!(r, -(-r));
}

#[test]
fn mul() {
    // identity
    let r: BaseElement = rand_value();
    assert_eq!(BaseElement::ZERO, r * BaseElement::ZERO);
    assert_eq!(r, r * BaseElement::ONE);

    // test multiplication within bounds
    assert_eq!(
        BaseElement::from(15u8),
        BaseElement::from(5u8) * BaseElement::from(3u8)
    );

    // test overflow
    let m = BaseElement::MODULUS;
    let t = BaseElement::from(m - 1);
    assert_eq!(BaseElement::ONE, t * t);
    assert_eq!(BaseElement::from(m - 2), t * BaseElement::from(2u8));
    assert_eq!(BaseElement::from(m - 4), t * BaseElement::from(4u8));

    let t = (m + 1) / 2;
    assert_eq!(
        BaseElement::ONE,
        BaseElement::from(t) * BaseElement::from(2u8)
    );
}

#[test]
fn exp() {
    let a = BaseElement::ZERO;
    assert_eq!(a.exp(0), BaseElement::ONE);
    assert_eq!(a.exp(1), BaseElement::ZERO);
    assert_eq!(a.exp7(), BaseElement::ZERO);

    let a = BaseElement::ONE;
    assert_eq!(a.exp(0), BaseElement::ONE);
    assert_eq!(a.exp(1), BaseElement::ONE);
    assert_eq!(a.exp(3), BaseElement::ONE);
    assert_eq!(a.exp7(), BaseElement::ONE);

    let a: BaseElement = rand_value();
    assert_eq!(a.exp(3), a * a * a);
    assert_eq!(a.exp(7), a.exp7());
}

#[test]
fn inv() {
    // identity
    assert_eq!(BaseElement::ONE, BaseElement::inv(BaseElement::ONE));
    assert_eq!(BaseElement::ZERO, BaseElement::inv(BaseElement::ZERO));
}

#[test]
fn element_as_int() {
    let v = u32::MAX;
    let e = BaseElement::new(v);
    assert_eq!(v % super::M, e.as_int() as u32);
}

#[test]
fn equals() {
    let a = BaseElement::ONE;
    let b = BaseElement::new(super::M - 1) * BaseElement::new(super::M - 1);

    // elements are equal
    assert_eq!(a, b);
    assert_eq!(a.as_int(), b.as_int());
    assert_eq!(a.to_bytes(), b.to_bytes());
}

// ROOTS OF UNITY
// ------------------------------------------------------------------------------------------------

#[test]
fn get_root_of_unity() {
    let root_13 = BaseElement::get_root_of_unity(13);
    assert_eq!(BaseElement::TWO_ADIC_ROOT_OF_UNITY, root_13);
    assert_eq!(BaseElement::ONE, root_13.exp(1u64 << 13));

    let root_12 = BaseElement::get_root_of_unity(12);
    let expected = root_13.exp(2);
    assert_eq!(expected, root_12);
    assert_eq!(BaseElement::ONE, root_12.exp(1u64 << 12));
}

// SERIALIZATION AND DESERIALIZATION
// ------------------------------------------------------------------------------------------------

#[test]
fn from_u128() {
    let v = u128::MAX;
    let e = BaseElement::from(v);
    assert_eq!((v % super::M as u128) as u64, e.as_int());
}

#[test]
fn try_from_slice() {
    let bytes = vec![1, 0, 0];
    let result = BaseElement::try_from(bytes.as_slice());
    assert!(result.is_ok());
    assert_eq!(1, result.unwrap().as_int());

    let bytes = vec![1, 0];
    let result = BaseElement::try_from(bytes.as_slice());
    assert!(result.is_err());

    let bytes = vec![1, 0, 0, 0];
    let result = BaseElement::try_from(bytes.as_slice());
    assert!(result.is_err());

    let bytes = vec![255, 255, 255];
    let result = BaseElement::try_from(bytes.as_slice());
    assert!(result.is_err());
}

// INITIALIZATION
// ------------------------------------------------------------------------------------------------

#[test]
fn zeroed_vector() {
    let result = BaseElement::zeroed_vector(4);
    assert_eq!(4, result.len());
    for element in result.into_iter() {
        assert_eq!(BaseElement::ZERO, element);
    }
}

// QUADRATIC EXTENSION
// ------------------------------------------------------------------------------------------------
#[test]
fn quad_mul() {
    // identity
    let r: QuadExtension<BaseElement> = rand_value();
    assert_eq!(
        <QuadExtension<BaseElement>>::ZERO,
        r * <QuadExtension<BaseElement>>::ZERO
    );
    assert_eq!(r, r * <QuadExtension<BaseElement>>::ONE);

    // TODO fix
    //// test multiplication within bounds
    //let a = <QuadExtension<BaseElement>>::new(BaseElement::new(3), BaseElement::ONE);
    //let b = <QuadExtension<BaseElement>>::new(BaseElement::new(4), BaseElement::new(2));
    //let expected = <QuadExtension<BaseElement>>::new(BaseElement::new(8), BaseElement::new(12));
    //assert_eq!(expected, a * b);

    //// test multiplication with overflow
    //let m = BaseElement::MODULUS as u32;
    //let a = <QuadExtension<BaseElement>>::new(BaseElement::new(3), BaseElement::new(m - 1));
    //let b = <QuadExtension<BaseElement>>::new(BaseElement::new(m - 3), BaseElement::new(5));
    //let expected = <QuadExtension<BaseElement>>::new(BaseElement::ONE, BaseElement::new(13));
    //assert_eq!(expected, a * b);

    //let a = <QuadExtension<BaseElement>>::new(BaseElement::new(3), BaseElement::new(m - 1));
    //let b = <QuadExtension<BaseElement>>::new(BaseElement::new(10), BaseElement::new(m - 2));
    //let expected = <QuadExtension<BaseElement>>::new(
    //    BaseElement::new(26),
    //    BaseElement::new(123), // TODO correct
    //);
    //assert_eq!(expected, a * b);
}

#[test]
fn quad_mul_base() {
    let a = <QuadExtension<BaseElement>>::new(rand_value(), rand_value());
    let b0 = rand_value();
    let b = <QuadExtension<BaseElement>>::new(b0, BaseElement::ZERO);

    let expected = a * b;
    assert_eq!(expected, a.mul_base(b0));
}

#[test]
fn quad_conjugate() {
    let m = BaseElement::MODULUS as u32;

    let a = <QuadExtension<BaseElement>>::new(BaseElement::new(m - 1), BaseElement::new(3));
    let expected = <QuadExtension<BaseElement>>::new(
        BaseElement::new(2),
        BaseElement::new(8380414),
    );
    assert_eq!(expected, a.conjugate());

    let a = <QuadExtension<BaseElement>>::new(BaseElement::new(m - 3), BaseElement::new(m - 2));
    let expected = <QuadExtension<BaseElement>>::new(
        BaseElement::new(8380412),
        BaseElement::new(2),
    );
    assert_eq!(expected, a.conjugate());

    let a = <QuadExtension<BaseElement>>::new(BaseElement::new(4), BaseElement::new(7));
    let expected = <QuadExtension<BaseElement>>::new(
        BaseElement::new(11),
        BaseElement::new(8380410),
    );
    assert_eq!(expected, a.conjugate());
}

// CUBIC EXTENSION
// ------------------------------------------------------------------------------------------------
#[test]
fn cube_mul() {
    // identity
    let r: CubeExtension<BaseElement> = rand_value();
    assert_eq!(
        <CubeExtension<BaseElement>>::ZERO,
        r * <CubeExtension<BaseElement>>::ZERO
    );
    assert_eq!(r, r * <CubeExtension<BaseElement>>::ONE);

    // TODO make tests
    //// test multiplication within bounds
    //let a = <CubeExtension<BaseElement>>::new(
    //    BaseElement::new(3),
    //    BaseElement::new(5),
    //    BaseElement::new(2),
    //);
    //let b = <CubeExtension<BaseElement>>::new(
    //    BaseElement::new(320),
    //    BaseElement::new(68),
    //    BaseElement::new(3),
    //);
    //let expected = <CubeExtension<BaseElement>>::new(
    //    BaseElement::new(1111),
    //    BaseElement::new(1961),
    //    BaseElement::new(995),
    //);
    //assert_eq!(expected, a * b);

    //// test multiplication with overflow
    //let a = <CubeExtension<BaseElement>>::new(
    //    BaseElement::new(4294967295),
    //    BaseElement::new(4223342345),
    //    BaseElement::new(4292343595),
    //);
    //let b = <CubeExtension<BaseElement>>::new(
    //    BaseElement::new(3342342342),
    //    BaseElement::new(4146435434),
    //    BaseElement::new(4222222595),
    //);
    //let expected = <CubeExtension<BaseElement>>::new(
    //    BaseElement::new(14070),
    //    BaseElement::new(123123),
    //    BaseElement::new(5970),
    //);
    //assert_eq!(expected, a * b);

    //let a = <CubeExtension<BaseElement>>::new(
    //    BaseElement::new(3342342342),
    //    BaseElement::new(3232323233),
    //    BaseElement::new(5268562),
    //);
    //let b = <CubeExtension<BaseElement>>::new(
    //    BaseElement::new(3333333542),
    //    BaseElement::new(1226),
    //    BaseElement::new(5346),
    //);
    //let expected = <CubeExtension<BaseElement>>::new(
    //    BaseElement::new(3342342342),
    //    BaseElement::new(2232325445),
    //    BaseElement::new(2444545456),
    //);
    //assert_eq!(expected, a * b);
}

#[test]
fn cube_mul_base() {
    let a = <CubeExtension<BaseElement>>::new(rand_value(), rand_value(), rand_value());
    let b0 = rand_value();
    let b = <CubeExtension<BaseElement>>::new(b0, BaseElement::ZERO, BaseElement::ZERO);

    let expected = a * b;
    assert_eq!(expected, a.mul_base(b0));
}

// RANDOMIZED TESTS
// ================================================================================================

proptest! {

    #[test]
    fn add_proptest(a in any::<u32>(), b in any::<u32>()) {
        let v1 = BaseElement::from(a);
        let v2 = BaseElement::from(b);
        let result = v1 + v2;

        let expected = (((a as u64) + (b as u64)) % (super::M as u64)) as u32;
        prop_assert_eq!(expected, result.as_int() as u32);
    }

    #[test]
    fn sub_proptest(a in any::<u32>(), b in any::<u32>()) {
        let v1 = BaseElement::from(a);
        let v2 = BaseElement::from(b);
        let result = v1 - v2;

        let a = a % (super::M as u32);
        let b = b % (super::M as u32);
        let expected = if a < b { super::M - b + a } else { a - b };

        prop_assert_eq!(expected, result.as_int() as u32);
    }

    #[test]
    fn neg_proptest(a in any::<u32>()) {
        let v = BaseElement::from(a);
        let expected = super::M - (a % super::M);

        prop_assert_eq!(expected, (-v).as_int() as u32);
    }

    #[test]
    fn mul_proptest(a in any::<u32>(), b in any::<u32>()) {
        let v1 = BaseElement::from(a);
        let v2 = BaseElement::from(b);
        let result = v1 * v2;

        let expected = (((a as u64) * (b as u64)) % super::M as u64) as u32;
        prop_assert_eq!(expected, result.as_int() as u32);
    }

    #[test]
    fn double_proptest(x in any::<u32>()) {
        let v = BaseElement::from(x);
        let result = v.double();

        let expected = (((x as u64) * 2) % super::M as u64) as u32;
        prop_assert_eq!(expected, result.as_int() as u32);
    }

    #[test]
    fn exp_proptest(a in any::<u32>(), b in any::<u32>()) {
        let result = BaseElement::from(a).exp(b as u64);

        let b = BigUint::from(b);
        let m = BigUint::from(super::M);
        let expected = BigUint::from(a).modpow(&b, &m).to_u32_digits()[0];
        prop_assert_eq!(expected, result.as_int() as u32);
    }

    #[test]
    fn inv_proptest(a in any::<u32>()) {
        let a = BaseElement::from(a);
        let b = a.inv();

        let expected = if a == BaseElement::ZERO { BaseElement::ZERO } else { BaseElement::ONE };
        prop_assert_eq!(expected, a * b);
    }

    #[test]
    fn element_as_int_proptest(a in any::<u32>()) {
        let e = BaseElement::new(a);
        prop_assert_eq!(a % super::M, e.as_int() as u32);
    }

    #[test]
    fn from_u128_proptest(v in any::<u64>()) {
        let e = BaseElement::from(v);
        assert_eq!((v % super::M as u64) as u32, e.as_int() as u32);
    }

    // QUADRATIC EXTENSION
    // --------------------------------------------------------------------------------------------
    #[test]
    fn quad_mul_inv_proptest(a0 in any::<u32>(), a1 in any::<u32>()) {
        let a = QuadExtension::<BaseElement>::new(BaseElement::from(a0), BaseElement::from(a1));
        let b = a.inv();

        let expected = if a == QuadExtension::<BaseElement>::ZERO {
            QuadExtension::<BaseElement>::ZERO
        } else {
            QuadExtension::<BaseElement>::ONE
        };
        prop_assert_eq!(expected, a * b);
    }

    // CUBIC EXTENSION
    // --------------------------------------------------------------------------------------------
    #[test]
    fn cube_mul_inv_proptest(a0 in any::<u32>(), a1 in any::<u32>(), a2 in any::<u32>()) {
        let a = CubeExtension::<BaseElement>::new(BaseElement::from(a0), BaseElement::from(a1), BaseElement::from(a2));
        let b = a.inv();

        let expected = if a == CubeExtension::<BaseElement>::ZERO {
            CubeExtension::<BaseElement>::ZERO
        } else {
            CubeExtension::<BaseElement>::ONE
        };
        prop_assert_eq!(expected, a * b);
    }
}
