// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.

mod quadratic;
pub use quadratic::QuadExtension;

mod cubic;
pub use cubic::CubeExtension;

mod sextic;
pub use sextic::SexticExtension;

use super::{ExtensibleField, ExtensionOf, FieldElement};
