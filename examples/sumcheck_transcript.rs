//! Synthetic example circuit that models repeated transcript + sumcheck verification structure.
use ff::Field;
use nova_snark::{
  frontend::{num::AllocatedNum, ConstraintSystem, SynthesisError},
  gadgets::ecc::AllocatedNonnativePoint,
  nova::{PublicParams, RecursiveSNARK},
  provider::{Bn256EngineIPA, GrumpkinEngine},
  traits::{
    circuit::StepCircuit, snark::RelaxedR1CSSNARKTrait, Engine, RO2ConstantsCircuit, ROCircuitTrait,
  },
};
use std::{marker::PhantomData, time::Instant};

#[derive(Clone, Copy, Debug)]
struct SumcheckSpec {
  rounds: usize,
  degree: usize,
  rlc_len: usize,
}

const TRANSCRIPT_SPECS: [SumcheckSpec; 4] = [
  SumcheckSpec {
    rounds: 32,
    degree: 9,
    rlc_len: 9,
  },
  SumcheckSpec {
    rounds: 28,
    degree: 6,
    rlc_len: 9,
  },
  SumcheckSpec {
    rounds: 32,
    degree: 3,
    rlc_len: 4,
  },
  SumcheckSpec {
    rounds: 32,
    degree: 3,
    rlc_len: 4,
  },
];

#[derive(Clone, Debug)]
struct SumcheckRoundWitness<S: ff::PrimeField> {
  coeffs: Vec<S>,
}

#[derive(Clone, Debug)]
struct SumcheckInstanceWitness<S: ff::PrimeField> {
  initial_claim: S,
  rounds: Vec<SumcheckRoundWitness<S>>,
  rlc_scalars: Vec<S>,
}

#[derive(Clone, Debug)]
struct TranscriptCircuitWitness<E: Engine> {
  transcripts: Vec<Vec<SumcheckInstanceWitness<E::Scalar>>>,
  final_points: Vec<(E::Base, E::Base, bool)>,
}

#[derive(Clone)]
struct TranscriptCircuit<E: Engine> {
  witness: TranscriptCircuitWitness<E>,
  ro_consts: RO2ConstantsCircuit<E>,
  _p: PhantomData<E>,
}

impl<E: Engine> TranscriptCircuit<E> {
  fn new() -> Self {
    let mut rng = rand::thread_rng();

    let mut make_instance = |spec: SumcheckSpec| {
      let mut rounds = Vec::with_capacity(spec.rounds);
      for _ in 0..spec.rounds {
        let coeffs = (0..=spec.degree)
          .map(|_| E::Scalar::random(&mut rng))
          .collect::<Vec<_>>();
        rounds.push(SumcheckRoundWitness { coeffs });
      }

      SumcheckInstanceWitness {
        initial_claim: E::Scalar::random(&mut rng),
        rounds,
        rlc_scalars: (0..spec.rlc_len)
          .map(|_| E::Scalar::random(&mut rng))
          .collect::<Vec<_>>(),
      }
    };

    // Two transcripts with 3 sumchecks each, then a fresh transcript with one sumcheck.
    let transcripts = vec![
      TRANSCRIPT_SPECS[..3]
        .iter()
        .map(|spec| make_instance(*spec))
        .collect(),
      TRANSCRIPT_SPECS[..3]
        .iter()
        .map(|spec| make_instance(*spec))
        .collect(),
      vec![make_instance(TRANSCRIPT_SPECS[3])],
    ];

    let final_points = (0..16)
      .map(|_| (E::Base::random(&mut rng), E::Base::random(&mut rng), false))
      .collect::<Vec<_>>();

    Self {
      witness: TranscriptCircuitWitness {
        transcripts,
        final_points,
      },
      ro_consts: RO2ConstantsCircuit::<E>::default(),
      _p: PhantomData,
    }
  }

  fn alloc_scalar<CS: ConstraintSystem<E::Scalar>>(
    mut cs: CS,
    value: E::Scalar,
    name: &str,
  ) -> Result<AllocatedNum<E::Scalar>, SynthesisError> {
    AllocatedNum::alloc(cs.namespace(|| name), || Ok(value))
  }

  fn enforce_equal<CS: ConstraintSystem<E::Scalar>>(
    mut cs: CS,
    a: &AllocatedNum<E::Scalar>,
    b: &AllocatedNum<E::Scalar>,
    name: &str,
  ) {
    cs.enforce(
      || name,
      |lc| lc + a.get_variable() - b.get_variable(),
      |lc| lc + CS::one(),
      |lc| lc,
    );
  }

  fn challenge_from_state<CS: ConstraintSystem<E::Scalar>>(
    &self,
    mut cs: CS,
    state: &AllocatedNum<E::Scalar>,
    tag: &AllocatedNum<E::Scalar>,
  ) -> Result<AllocatedNum<E::Scalar>, SynthesisError> {
    let mut ro = E::RO2Circuit::new(self.ro_consts.clone());
    ro.absorb(state);
    ro.absorb(tag);
    ro.squeeze_scalar(cs.namespace(|| "squeeze challenge"))
  }

  fn random_linear_combination<CS: ConstraintSystem<E::Scalar>>(
    mut cs: CS,
    challenge: &AllocatedNum<E::Scalar>,
    scalars: &[AllocatedNum<E::Scalar>],
  ) -> Result<AllocatedNum<E::Scalar>, SynthesisError> {
    // scalar_0 + challenge * scalar_1 + challenge^2 * scalar_2 + ...
    let mut power = AllocatedNum::alloc(cs.namespace(|| "challenge^0"), || Ok(E::Scalar::ONE))?;
    cs.enforce(
      || "bind challenge^0",
      |lc| lc + power.get_variable(),
      |lc| lc + CS::one(),
      |lc| lc + CS::one(),
    );

    let mut acc = AllocatedNum::alloc(cs.namespace(|| "rlc init"), || Ok(E::Scalar::ZERO))?;
    cs.enforce(
      || "bind rlc init",
      |lc| lc + acc.get_variable(),
      |lc| lc + CS::one(),
      |lc| lc,
    );

    for (i, scalar) in scalars.iter().enumerate() {
      let term = power.mul(cs.namespace(|| format!("rlc term mul {i}")), scalar)?;
      acc = acc.add(cs.namespace(|| format!("rlc term add {i}")), &term)?;
      power = power.mul(cs.namespace(|| format!("power update {i}")), challenge)?;
    }

    Ok(acc)
  }

  fn eval_poly<CS: ConstraintSystem<E::Scalar>>(
    mut cs: CS,
    coeffs: &[AllocatedNum<E::Scalar>],
    x: &AllocatedNum<E::Scalar>,
  ) -> Result<AllocatedNum<E::Scalar>, SynthesisError> {
    let mut power = AllocatedNum::alloc(cs.namespace(|| "x^0"), || Ok(E::Scalar::ONE))?;
    cs.enforce(
      || "bind x^0",
      |lc| lc + power.get_variable(),
      |lc| lc + CS::one(),
      |lc| lc + CS::one(),
    );

    let mut acc = AllocatedNum::alloc(cs.namespace(|| "poly init"), || Ok(E::Scalar::ZERO))?;
    cs.enforce(
      || "bind poly init",
      |lc| lc + acc.get_variable(),
      |lc| lc + CS::one(),
      |lc| lc,
    );

    for (i, c) in coeffs.iter().enumerate() {
      let term = power.mul(cs.namespace(|| format!("poly term mul {i}")), c)?;
      acc = acc.add(cs.namespace(|| format!("poly term add {i}")), &term)?;
      power = power.mul(cs.namespace(|| format!("poly power update {i}")), x)?;
    }

    Ok(acc)
  }
}

impl<E: Engine> StepCircuit<E::Scalar> for TranscriptCircuit<E> {
  fn arity(&self) -> usize {
    1
  }

  fn synthesize<CS: ConstraintSystem<E::Scalar>>(
    &self,
    cs: &mut CS,
    z_in: &[AllocatedNum<E::Scalar>],
  ) -> Result<Vec<AllocatedNum<E::Scalar>>, SynthesisError> {
    assert_eq!(z_in.len(), 1);

    let mut transcript_counter = 0usize;
    let mut transcript_state = z_in[0].clone();

    for (t_idx, transcript_instances) in self.witness.transcripts.iter().enumerate() {
      if t_idx == 2 {
        // New transcript.
        transcript_state = Self::alloc_scalar(
          cs.namespace(|| "new transcript state"),
          E::Scalar::ZERO,
          "transcript reset",
        )?;
      }

      for (inst_idx, inst) in transcript_instances.iter().enumerate() {
        let mut claim = Self::alloc_scalar(
          cs.namespace(|| format!("transcript {t_idx} inst {inst_idx} initial claim")),
          inst.initial_claim,
          "claim",
        )?;

        for (round_idx, round) in inst.rounds.iter().enumerate() {
          let coeffs = round
            .coeffs
            .iter()
            .enumerate()
            .map(|(i, c)| {
              Self::alloc_scalar(
                cs.namespace(|| {
                  format!("transcript {t_idx} inst {inst_idx} round {round_idx} coeff {i}")
                }),
                *c,
                "coeff",
              )
            })
            .collect::<Result<Vec<_>, _>>()?;

          // Sumcheck verifier check: current claim equals g(0) + g(1).
          let g0 = coeffs[0].clone();
          let mut g1 = Self::alloc_scalar(
            cs.namespace(|| {
              format!("transcript {t_idx} inst {inst_idx} round {round_idx} g1 init")
            }),
            E::Scalar::ZERO,
            "g1 init",
          )?;
          cs.enforce(
            || format!("bind g1 init {t_idx}-{inst_idx}-{round_idx}"),
            |lc| lc + g1.get_variable(),
            |lc| lc + CS::one(),
            |lc| lc,
          );
          for (i, c) in coeffs.iter().enumerate() {
            g1 = g1.add(
              cs.namespace(|| format!("g1 accumulation {t_idx}-{inst_idx}-{round_idx}-{i}")),
              c,
            )?;
          }
          let g0_plus_g1 = g0.add(
            cs.namespace(|| format!("g0_plus_g1 {t_idx}-{inst_idx}-{round_idx}")),
            &g1,
          )?;
          Self::enforce_equal(
            cs.namespace(|| format!("sumcheck claim check {t_idx}-{inst_idx}-{round_idx}")),
            &claim,
            &g0_plus_g1,
            "claim consistency",
          );

          let round_tag = Self::alloc_scalar(
            cs.namespace(|| format!("challenge tag {t_idx}-{inst_idx}-{round_idx}")),
            E::Scalar::from((transcript_counter + round_idx + 1) as u64),
            "tag",
          )?;
          let challenge = self.challenge_from_state(
            cs.namespace(|| format!("challenge derive {t_idx}-{inst_idx}-{round_idx}")),
            &transcript_state,
            &round_tag,
          )?;

          claim = Self::eval_poly(
            cs.namespace(|| format!("eval g(r) {t_idx}-{inst_idx}-{round_idx}")),
            &coeffs,
            &challenge,
          )?;
          transcript_state = claim.clone();
        }

        let rlc_tag = Self::alloc_scalar(
          cs.namespace(|| format!("rlc tag {t_idx}-{inst_idx}")),
          E::Scalar::from((1000 + transcript_counter) as u64),
          "rlc tag",
        )?;
        let rlc_challenge = self.challenge_from_state(
          cs.namespace(|| format!("derive rlc challenge {t_idx}-{inst_idx}")),
          &transcript_state,
          &rlc_tag,
        )?;

        let rlc_scalars = inst
          .rlc_scalars
          .iter()
          .enumerate()
          .map(|(i, v)| {
            Self::alloc_scalar(
              cs.namespace(|| format!("rlc scalar {t_idx}-{inst_idx}-{i}")),
              *v,
              "rlc scalar",
            )
          })
          .collect::<Result<Vec<_>, _>>()?;

        transcript_state = Self::random_linear_combination(
          cs.namespace(|| format!("rlc compute {t_idx}-{inst_idx}")),
          &rlc_challenge,
          &rlc_scalars,
        )?;

        transcript_counter += 1;
      }
    }

    // Final Poseidon-based RO hash of 16 nonnative points (foreign field elements).
    let mut ro = E::RO2Circuit::new(self.ro_consts.clone());
    for (i, point) in self.witness.final_points.iter().enumerate() {
      let p = AllocatedNonnativePoint::<E>::alloc(
        cs.namespace(|| format!("final point {i}")),
        Some(*point),
      )?;
      p.absorb_in_ro(cs.namespace(|| format!("absorb final point {i}")), &mut ro)?;
    }
    let points_hash = ro.squeeze_scalar(cs.namespace(|| "final point hash"))?;

    let z_out = transcript_state.add(cs.namespace(|| "output combine"), &points_hash)?;
    Ok(vec![z_out])
  }
}

type E1 = Bn256EngineIPA;
type E2 = GrumpkinEngine;
type EE1 = nova_snark::provider::ipa_pc::EvaluationEngine<E1>;
type EE2 = nova_snark::provider::ipa_pc::EvaluationEngine<E2>;
type S1 = nova_snark::spartan::snark::RelaxedR1CSSNARK<E1, EE1>;
type S2 = nova_snark::spartan::snark::RelaxedR1CSSNARK<E2, EE2>;

fn main() {
  println!("=========================================================");
  println!("Synthetic transcript + sumcheck verifier example");
  println!("=========================================================");

  let circuit = TranscriptCircuit::<E1>::new();

  let start = Instant::now();
  let pp = PublicParams::<E1, E2, TranscriptCircuit<E1>>::setup(
    &circuit,
    &*S1::ck_floor(),
    &*S2::ck_floor(),
  )
  .expect("public params setup should succeed");
  println!("PublicParams::setup took {:?}", start.elapsed());

  println!(
    "Number of constraints per step (primary, secondary): {:?}",
    pp.num_constraints()
  );
  println!(
    "Number of variables per step (primary, secondary): {:?}",
    pp.num_variables()
  );

  let mut recursive_snark = RecursiveSNARK::<E1, E2, TranscriptCircuit<E1>>::new(
    &pp,
    &circuit,
    &[<E1 as Engine>::Scalar::ZERO],
  )
  .expect("initialize recursive snark");

  let start = Instant::now();
  recursive_snark
    .prove_step(&pp, &circuit)
    .expect("first prove step should succeed");
  println!(
    "RecursiveSNARK::prove_step (1 step) took {:?}",
    start.elapsed()
  );
}
