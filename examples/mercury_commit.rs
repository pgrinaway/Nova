//! Demonstrates committing to a multilinear polynomial with the Mercury commitment scheme.
//!
//! Run with a small log2 size:
//! `cargo run --example mercury_commit -- 3`
use std::env;

use halo2curves::{bn256::Fr, ff::Field};
use nova_snark::{
  provider::{mercury::EvaluationEngine as MercuryEvaluationEngine, Bn256EngineKZG},
  spartan::polys::multilinear::MultilinearPolynomial,
  traits::{
    commitment::CommitmentEngineTrait, evaluation::EvaluationEngineTrait, Engine,
    TranscriptEngineTrait,
  },
};
use rand_core::OsRng;

fn parse_log_n() -> usize {
  let mut args = env::args().skip(1);
  let log_n = match args.next() {
    Some(value) => value.parse::<usize>().unwrap_or_else(|_| {
      eprintln!("Expected a usize for log2 polynomial size (e.g., 3).");
      std::process::exit(1);
    }),
    None => 3,
  };

  if log_n == 0 {
    eprintln!("log2 polynomial size must be at least 1.");
    std::process::exit(1);
  }

  log_n
}

fn main() {
  let log_n = parse_log_n();
  let n = 1usize << log_n;

  type E = Bn256EngineKZG;
  type EE = MercuryEvaluationEngine<E>;

  let coeffs: Vec<Fr> = (0..n).map(|_| Fr::random(OsRng)).collect();
  let poly = MultilinearPolynomial::new(coeffs.clone());
  let point: Vec<Fr> = (0..log_n).map(|_| Fr::random(OsRng)).collect();
  let eval = poly.evaluate(&point);

  let ck = <<E as Engine>::CE as CommitmentEngineTrait<E>>::CommitmentKey::setup_from_rng(
    b"mercury-example",
    n,
    OsRng,
  );
  let (pk, vk) = EE::setup(&ck);
  let comm = <E as Engine>::CE::commit(&ck, &coeffs, &Fr::ZERO);

  let mut transcript = <E as Engine>::TE::new(b"mercury-example");
  let arg = EE::prove(&ck, &pk, &mut transcript, &comm, &coeffs, &point, &eval)
    .expect("mercury proof should succeed");

  let mut transcript = <E as Engine>::TE::new(b"mercury-example");
  EE::verify(&vk, &mut transcript, &comm, &point, &eval, &arg)
    .expect("mercury verification should succeed");

  println!(
    "Committed to a {n}-point multilinear polynomial (log2 size = {log_n})."
  );
}
