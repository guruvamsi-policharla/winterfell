// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.

use crate::{Example, ExampleOptions, perm_raps::prover::PermRapsProver};
use log::debug;
use polynomials::Polynomial;
use std::time::Instant;
use winterfell::{
    math::{fields::f128::BaseElement, log2, ExtensionOf, FieldElement},
    ProofOptions, Prover, StarkProof, Trace, VerifierError,
};

mod custom_trace_table;
pub use custom_trace_table::RapTraceTable;

mod air;
use air::{PublicInputs, PermRapsAir};

mod prover;

#[cfg(test)]
mod tests;

// CONSTANTS
// ================================================================================================

const MAIN_WIDTH: usize = 4;
const AUX_WIDTH: usize = 5;
// RESCUE SPLIT HASH CHAIN EXAMPLE
// ================================================================================================

pub fn get_example(options: ExampleOptions, chain_length: usize) -> Box<dyn Example> {
    Box::new(PermRapsExample::new(
        chain_length,
        options.to_proof_options(42, 4),
    ))
}

pub struct PermRapsExample {
    options: ProofOptions,
    chain_length: usize,
    p: Vec<BaseElement>,
    q: Vec<BaseElement>,
    r: Vec<BaseElement>,
}

impl PermRapsExample {
    pub fn new(chain_length: usize, options: ProofOptions) -> PermRapsExample {
        assert!(
            chain_length.is_power_of_two(),
            "chain length must a power of 2"
        );
        assert!(chain_length > 2, "chain length must be at least 4");

        // Schoolbook polynomial multiplication
        let mut ppoly = Polynomial::<u32>::new();
        let mut qpoly = Polynomial::<u32>::new();
        for i in 0..chain_length-1{
            ppoly.push(i as u32);
            qpoly.push(2*i as u32);
        }

        ppoly.push(0);
        qpoly.push(0);
        
        let rpoly = ppoly.clone()*qpoly.clone();

        let mut p: Vec<BaseElement>  = Vec::new();
        let mut q: Vec<BaseElement>  = Vec::new();
        let mut r: Vec<BaseElement>  = Vec::new();
        
        for coeff in ppoly.iter(){
            p.push(BaseElement::from(*coeff));
        }
        for coeff in qpoly.iter(){
            q.push(BaseElement::from(*coeff));
        }
        for coeff in rpoly.iter(){
            r.push(BaseElement::from(*coeff));
        }
        r.push(BaseElement::ZERO);
        
        PermRapsExample {
            options,
            chain_length,
            p,
            q,
            r
        }
    }
}

// EXAMPLE IMPLEMENTATION
// ================================================================================================

impl Example for PermRapsExample {
    fn prove(&self) -> StarkProof {
        // generate the execution trace
        debug!(
            "Generating proof for computing a chain of {} Rescue hashes\n\
            ---------------------",
            self.chain_length
        );

        // create a prover
        let prover = PermRapsProver::new(self.options.clone());

        // generate the execution trace
        let now = Instant::now();
        let trace = prover.build_trace(&self.p, &self.q, &self.r);
        let trace_length = trace.length();
        debug!(
            "Generated execution trace of {} registers and 2^{} steps in {} ms",
            trace.width(),
            log2(trace_length),
            now.elapsed().as_millis()
        );

        // generate the proof
        prover.prove(trace).unwrap()
    }

    fn verify(&self, proof: StarkProof) -> Result<(), VerifierError> {
        let pub_inputs = PublicInputs {
            result: [[BaseElement::ZERO; 2]; 2],
        };
        winterfell::verify::<PermRapsAir>(proof, pub_inputs)
    }

    fn verify_with_wrong_inputs(&self, proof: StarkProof) -> Result<(), VerifierError> {
        let pub_inputs = PublicInputs {
            result: [[BaseElement::ZERO; 2]; 2],
        };
        winterfell::verify::<PermRapsAir>(proof, pub_inputs)
    }
}