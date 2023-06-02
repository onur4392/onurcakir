//! Benchmarks Nova's prover for proving SHA-256 with varying sized messages.
//! We run a single step with the step performing the entire computation.
//! This code invokes a hand-written SHA-256 gadget from bellman/bellperson.
//! It also uses code from bellman/bellperson to compare circuit-generated digest with sha2 crate's output
#![allow(non_snake_case)]
type G1 = pasta_curves::pallas::Point;
type G2 = pasta_curves::vesta::Point;
use ::bellperson::{
  gadgets::{
    boolean::{AllocatedBit, Boolean},
    num::{AllocatedNum, Num},
    //sha256::sha256,
    sha256::sha256iterated,
    Assignment,
  },
  ConstraintSystem, SynthesisError,
};
use ff::{PrimeField, PrimeFieldBits};
use hex_literal::hex;
use nova_snark::{
  traits::{
    circuit::{StepCircuit, TrivialTestCircuit},
    Group,
  },
  PublicParams, RecursiveSNARK,
};
use sha2::{Digest, Sha256};
use criterion::*;
use core::time::Duration;

use crate::traits::{ROCircuitTrait, ROConstantsTrait, ROTrait};
use generic_array::typenum::U24;
use neptune::{
  circuit2::Elt,
  poseidon::PoseidonConstants,
  sponge::{
    api::{IOPattern, SpongeAPI, SpongeOp},
    circuit::SpongeCircuit,
    vanilla::{Mode::Simplex, Sponge, SpongeTrait},
  },
  Strength,
};

#[derive(Clone)]
pub struct PoseidonConstantsCircuit<Scalar: PrimeField>(PoseidonConstants<Scalar, U24>);

impl<Scalar> ROConstantsTrait<Scalar> for PoseidonConstantsCircuit<Scalar>
where
  Scalar: PrimeField + PrimeFieldBits,
{
  /// Generate Poseidon constants
  #[allow(clippy::new_without_default)]
  fn new() -> Self {
    Self(Sponge::<Scalar, U24>::api_constants(Strength::Standard))
  }
}

const NITERATIONS: u32 = 3;

#[derive(Clone, Debug)]
struct Sha256CircuitOrig<Scalar: PrimeField> {
  preimage: Vec<u8>,
  digest: Scalar,
}

#[derive(Clone, Debug)]
struct Sha256Circuit<Scalar: PrimeField> {
  preimage: Vec<u8>,
  digest: Vec<Scalar>,
}

impl<Scalar: PrimeField + PrimeFieldBits> StepCircuit<Scalar> for Sha256Circuit<Scalar> {
    fn arity(&self) -> usize {
	1
    }

    fn synthesize<CS: ConstraintSystem<Scalar>>(
	&self,
	cs: &mut CS,
	_z: &[AllocatedNum<Scalar>],
    ) -> Result<Vec<AllocatedNum<Scalar>>, SynthesisError> {

	assert_eq!(self.preimage.len(), 64 * (NITERATIONS as usize));
	
	let mut z_out: Vec<AllocatedNum<Scalar>> = Vec::new();

	let bit_values: Vec<_> =	  
	    self.preimage.clone().into_iter().flat_map(|byte| (0..8).map(move |i| (byte >> i) & 1u8 == 1u8)).map(Some).collect();
	assert_eq!(bit_values.len(), self.preimage.len() * 8);

	let preimage_bits = bit_values
	    .into_iter()
	    .enumerate()
	    .map(|(i, b)| AllocatedBit::alloc(cs.namespace(|| format!("preimage bit {i}")), b))
	    .map(|b| b.map(Boolean::from))
	    .collect::<Result<Vec<_>, _>>()?;

//	let hash_bits = sha256(cs.namespace(|| "sha256"), &preimage_bits)?;
	let niterations: u32 = NITERATIONS;
	let hash_bits = sha256iterated(cs.namespace(|| "sha256"), &preimage_bits, niterations)?;

	println!("hash_bits length {:?}", hash_bits.len());
	
	for (i, hash_bits) in hash_bits.chunks(256_usize).enumerate() {
	    let mut num = Num::<Scalar>::zero();
	    let mut coeff = Scalar::one();
	    for bit in hash_bits {
		num = num.add_bool_with_coeff(CS::one(), bit, coeff);

		coeff = coeff.double();
	    }

	    let hash = AllocatedNum::alloc(cs.namespace(|| format!("input {i}")), || {
		Ok(*num.get_value().get()?)
	    })?;

	    // num * 1 = hash
	    cs.enforce(
		|| format!("packing constraint {i}"),
		|_| num.lc(Scalar::one()),
		|lc| lc + CS::one(),
		|lc| lc + hash.get_variable(),
	    );
	    z_out.push(hash);
	}

	// apply Poseidon
        let constants = PoseidonConstantsCircuit::new();

	// sanity check with the hasher
	let mut hasher = Sha256::new();
	hasher.update(&self.preimage);
	let hash_result = hasher.finalize();

	let mut s = hash_result
	    .iter()
	    .flat_map(|&byte| (0..8).rev().map(move |i| (byte >> i) & 1u8 == 1u8));

	// truncate to the first 256 elements which corresponds to the
	// first hash value returned by sha256iterated
	let mut hash_bits_slice = hash_bits;
	hash_bits_slice.truncate(256);

	for b in &hash_bits_slice {
	    match b {
		Boolean::Is(b) => {
		    assert!(s.next().unwrap() == b.get_value().unwrap());
		}
		Boolean::Not(b) => {
		    assert!(s.next().unwrap() != b.get_value().unwrap());
		}
		Boolean::Constant(_b) => {
		    panic!("Can't reach here")
		}
	    }
	}

	println!("hash_bits_slice length {:?}", hash_bits_slice.len());
	println!("z_out length {:?}", z_out.len());
	Ok(z_out)
    }

    fn output(&self, _z: &[Scalar]) -> Vec<Scalar> {
	//vec![self.digest]
	self.digest.clone()
    }
}

type C1 = Sha256Circuit<<G1 as Group>::Scalar>;
type C2 = TrivialTestCircuit<<G2 as Group>::Scalar>;

criterion_group! {
name = recursive_snark;
config = Criterion::default().warm_up_time(Duration::from_millis(3000));
targets = bench_recursive_snark
}

criterion_main!(recursive_snark);

fn bench_recursive_snark(c: &mut Criterion) {
    let bytes_to_scalar = |bytes: [u8; 32]| -> <G1 as Group>::Scalar {
	let mut bytes_le = bytes;
	bytes_le.reverse();
	<G1 as Group>::Scalar::from_repr(bytes_le).unwrap()
    };

    // Test vectors
    let circuit_primary =
	Sha256Circuit {
	    preimage: vec![0u8; 64 * (NITERATIONS as usize)],
	    digest: vec![bytes_to_scalar(hex!(
		"12df9ae4958c1957170f9b04c4bc00c27315c5d75a391f4b672f952842bfa5ac"
	    )); NITERATIONS as usize],
	};

    // let vec = vec![0; 5];
    
//    let mut group = c.benchmark_group(format!("NovaProve-Sha256-message-len-{}", circuit_primary.preimage.len()));
//    group.sample_size(10);

    // Produce public parameters
    let pp = PublicParams::<G1, G2, C1, C2>::setup(
	circuit_primary.clone(),
	TrivialTestCircuit::default(),
    );
    println!(
      "Number of constraints per step (primary circuit): {}",
      pp.num_constraints().0
    );
    println!(
      "Number of constraints per step (secondary circuit): {}",
      pp.num_constraints().1
    );

    println!(
      "Number of variables per step (primary circuit): {}",
      pp.num_variables().0
    );
    println!(
      "Number of variables per step (secondary circuit): {}",
      pp.num_variables().1
    );
    /*
    let num_steps = 10;
    let sha256_circuits = (0..num_steps)
        .map(|_| Sha256Circuit {
	    preimage: vec![0u8; 64],
	    digest: bytes_to_scalar(hex!(
		"12df9ae4958c1957170f9b04c4bc00c27315c5d75a391f4b672f952842bfa5ac"
	    )),	    
      })
    .collect::<Vec<_>>();
    */
    /*    
    let mut group = c.benchmark_group(format!("NovaProve-Sha256-message-len-{}", circuit_primary.preimage.len()));
    group.sample_size(10);
    group.bench_function("Prove", |b| {
	b.iter(|| {
	    // produce a recursive SNARK for a step of the recursion
	    assert!(RecursiveSNARK::prove_step(
		black_box(&pp),
		black_box(None),
		black_box(circuit_primary.clone()),
		black_box(TrivialTestCircuit::default()),
		black_box(vec![<G1 as Group>::Scalar::from(2u64)]),
		black_box(vec![<G2 as Group>::Scalar::from(2u64)]),
	    )
		    .is_ok());
	})
    });
    group.finish();
    */
}
