//! Demonstrates field multiplication over the scalar field used in the Mercury example.
//!
//! Run with a small log2 size:
//! `cargo run --example field_mul -- 3`
use std::env;

use halo2curves::{bn256::Fr, ff::Field};
use rand_core::OsRng;

fn parse_log_n() -> usize {
  let mut args = env::args().skip(1);
  let log_n = match args.next() {
    Some(value) => value.parse::<usize>().unwrap_or_else(|_| {
      eprintln!("Expected a usize for log2 vector size (e.g., 3).");
      std::process::exit(1);
    }),
    None => 3,
  };

  if log_n == 0 {
    eprintln!("log2 vector size must be at least 1.");
    std::process::exit(1);
  }

  log_n
}

fn main() {
  let log_n = parse_log_n();
  let n = 1usize << log_n;

  let base = Fr::random(OsRng);
  let elements: Vec<Fr> = (0..n).map(|_| Fr::random(OsRng)).collect();
  let products: Vec<Fr> = elements.iter().map(|value| *value * base).collect();

  println!(
    "Multiplied {n} random field elements by a base scalar (log2 size = {log_n})."
  );

  let checksum = products
    .iter()
    .fold(Fr::ZERO, |acc, value| acc + value);
  println!("Checksum: {checksum:?}");
}
