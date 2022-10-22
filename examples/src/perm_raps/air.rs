// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.

use super::{
    BaseElement, ExtensionOf, FieldElement, ProofOptions, MAIN_WIDTH, AUX_WIDTH
};
use crate::utils::{are_equal};
use winterfell::{
    Air, AirContext, Assertion, AuxTraceRandElements, ByteWriter, EvaluationFrame, Serializable,
    TraceInfo, TransitionConstraintDegree,
};

// CONSTANTS
// ================================================================================================


// RESCUE AIR
// ================================================================================================

pub struct PublicInputs {
    pub result: [[BaseElement; 2]; 2],
}

impl Serializable for PublicInputs {
    fn write_into<W: ByteWriter>(&self, target: &mut W) {
        target.write(&self.result[..]);
    }
}

pub struct PermRapsAir {
    context: AirContext<BaseElement>,
}

impl Air for PermRapsAir {
    type BaseField = BaseElement;
    type PublicInputs = PublicInputs;

    // CONSTRUCTOR
    // --------------------------------------------------------------------------------------------
    fn new(trace_info: TraceInfo, _pub_inputs: PublicInputs, options: ProofOptions) -> Self {
        let main_degrees = 
            vec![TransitionConstraintDegree::new(1); 1];
            // vec![TransitionConstraintDegree::with_cycles(3, vec![CYCLE_LENGTH]); 2 * STATE_WIDTH];
        let aux_degrees = vec![
            TransitionConstraintDegree::new(2),
            TransitionConstraintDegree::new(2),
            TransitionConstraintDegree::new(2),
            TransitionConstraintDegree::new(1),
            TransitionConstraintDegree::new(1),
        ];
        assert_eq!(MAIN_WIDTH+AUX_WIDTH, trace_info.width());
        PermRapsAir {
            context: AirContext::new_multi_segment(
                trace_info,
                main_degrees,
                aux_degrees,
                2,
                2,
                options,
            ),
        }
    }

    fn context(&self) -> &AirContext<Self::BaseField> {
        &self.context
    }

    fn evaluate_transition<E: FieldElement + From<Self::BaseField>>(
        &self,
        frame: &EvaluationFrame<E>,
        _periodic_values: &[E],
        _result: &mut [E],
    ) {
        let current = frame.current();
        let next = frame.next();
        
        debug_assert_eq!(MAIN_WIDTH, current.len());
        debug_assert_eq!(MAIN_WIDTH, next.len());
    }

    fn evaluate_aux_transition<F, E>(
        &self,
        main_frame: &EvaluationFrame<F>,
        aux_frame: &EvaluationFrame<E>,
        _periodic_values: &[F],
        aux_rand_elements: &AuxTraceRandElements<E>,
        result: &mut [E],
    ) where
        F: FieldElement<BaseField = Self::BaseField>,
        E: FieldElement<BaseField = Self::BaseField> + ExtensionOf<F>,
    {
        let main_current = main_frame.current();
        let main_next = main_frame.next();

        let aux_current = aux_frame.current();
        let aux_next = aux_frame.next();

        debug_assert_eq!(MAIN_WIDTH, main_current.len());
        debug_assert_eq!(MAIN_WIDTH, main_next.len());

        debug_assert_eq!(AUX_WIDTH, aux_current.len());
        debug_assert_eq!(AUX_WIDTH, aux_next.len());

        let random_elements = aux_rand_elements.get_segment_elements(0);

        result[0] = are_equal(
            aux_next[0],
            aux_current[0] + aux_current[3]*main_current[0].into(),
        );

        result[1] = are_equal(
            aux_next[1],
            aux_current[1] + aux_current[3]*main_current[1].into(),
        );

        result[2] = are_equal(
            aux_next[2],
            aux_current[2] + aux_current[3]*main_current[2].into() + aux_current[4]*main_current[3].into(),
        );

        result[3] = are_equal(
            aux_next[3],
            aux_current[3]*random_elements[0],
        );

        result[4] = are_equal(
            aux_next[4],
            aux_current[4]*random_elements[0],
        );
    }

    fn get_assertions(&self) -> Vec<Assertion<Self::BaseField>> {
        // Assert starting and ending values of the hash chain
        let last_step = self.trace_length() - 1;
        vec![
            // Last registers of original and permuted columnset to zero
            Assertion::single(0, last_step, BaseElement::ZERO),
            Assertion::single(1, last_step, BaseElement::ZERO),
        ]
    }

    fn get_aux_assertions<E: FieldElement + From<Self::BaseField>>(
        &self,
        _aux_rand_elements: &AuxTraceRandElements<E>,
    ) -> Vec<Assertion<E>> {
        // let last_step = self.trace_length() - 1;
        vec![
            Assertion::single(0, 0, E::ZERO),
            Assertion::single(1, 0, E::ZERO),
        ]
    }

    fn get_periodic_column_values(&self) -> Vec<Vec<Self::BaseField>> {
        let mut absorption_column = vec![BaseElement::ZERO; 16];
        absorption_column[14] = BaseElement::ONE;
        let result = vec![absorption_column];

        result
    }
}