// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.

use winterfell::{math::FieldElement};

use crate::perm_raps::MAIN_WIDTH;

use super::{
    BaseElement, ProofOptions,
    Prover, PublicInputs, RapTraceTable, PermRapsAir,
};

// RESCUE PROVER
// ================================================================================================

pub struct PermRapsProver {
    options: ProofOptions,
}

impl PermRapsProver {
    pub fn new(options: ProofOptions) -> Self {
        Self { options }
    }

    pub fn build_trace(
        &self,
        p: &[BaseElement],
        q: &[BaseElement],
        r: &[BaseElement],
    ) -> RapTraceTable<BaseElement> {
        // sanity checks
        debug_assert_eq!(p.len(), q.len());
        debug_assert_eq!(2*p.len(), r.len());
        
        // allocate memory to hold the trace table
        let trace_length = p.len();
        let mut trace = RapTraceTable::new(MAIN_WIDTH, trace_length);

        trace.fill(
            |state| {
                // insert coefficients
                state[0] = p[0];
                state[1] = q[0];
                
                state[2] = r[0];
                state[3] = r[trace_length];
                // println!("{}, {}", 0, trace_length-1);
            },
            |step, state| {
                if step+1 == trace_length-1{
                    // insert zero at the bottom of the table
                    state[0] = BaseElement::ZERO;
                    state[1] = BaseElement::ZERO;

                    state[2] = BaseElement::ZERO;
                    state[3] = BaseElement::ZERO;
                } else{
                    // insert coefficients
                    state[0] = p[step+1];
                    state[1] = q[step+1];

                    state[2] = r[step+1];
                    state[3] = r[step+trace_length];
                    // println!("{}, {}", step+1, step+trace_length);
                }

                
            },
        );
        
        trace
    }
}

impl Prover for PermRapsProver {
    type BaseField = BaseElement;
    type Air = PermRapsAir;
    type Trace = RapTraceTable<BaseElement>;

    fn get_pub_inputs(&self, _trace: &Self::Trace) -> PublicInputs {
        PublicInputs {
            result: [[BaseElement::ZERO; 2]; 2],
        }
    }

    fn options(&self) -> &ProofOptions {
        &self.options
    }
}
