# Experimental features

In `privacy-scaling-explorations/halo2` fork we have implemented many experimental features to cover different use cases, especially for those with huge circuits. We collect them in this page for easier tracking and referencing.

## Commitment scheme abstraction

To support different kind of polynomial commitment scheme, we added a trait `CommitmentScheme` to allow create/verify proof with different commitment scheme implementation, currently there are 2 available implementations in this fork:

- `IPACommitmentScheme`

  The original implementation from `zcash/halo2` with the original multi-open strategy `{Prover,Verifier}IPA`

- `KZGCommitmentScheme`

  KZG commitment scheme as in [GWC19](https://eprint.iacr.org/2019/953), which doesn't commit the instance columns, with 2 multi-open strategies available:

  - `{Prover,Verifier}GWC` - The original strategy in [GWC19](https://eprint.iacr.org/2019/953)
  - `{Prover,Verifier}SHPLONK` - The strategy proposed in [BDFG20](https://eprint.iacr.org/2020/081)

When using `create_proof` and `verify_proof`, we need to specify the commitment scheme and multi-open strategy like:

```rust
// Using IPA
create_proof<IPACommitmentScheme<_>, ProverIPA<_>, _, _, _, _>
verify_proof<IPACommitmentScheme<_>, ProverIPA<_>, _, _, _>

// Using KZG with GWC19 mutli-open strategy
create_proof<KZGCommitmentScheme<_>, ProverGWC<_>, _, _, _, _>
verify_proof<KZGCommitmentScheme<_>, ProverGWC<_>, _, _, _>

// Using KZG with BDFG20 mutli-open strategy
create_proof<KZGCommitmentScheme<_>, ProverSHPLONK<_>, _, _, _, _>
verify_proof<KZGCommitmentScheme<_>, ProverSHPLONK<_>, _, _, _>
```

## `ConstraintSystem` extension

### Dynamic lookup

`ConstraintSystem::lookup_any` is added for use cases that need to lookup dynamic table instead of fixed table.

Unlike `ConstraintSystem::lookup` which only allows `TableColumn`(s) as table, it allows any `Expression`(s) without simple selector.

### Shuffle

`ConstraintSystem::shuffle` is added for use cases that only need shuffle without pre-defined mapping.

It allows us to prove any `Expression`(s) without simple selector is shuffled from the other.

### Multi-phase

`ConstraintSystem::advice_column_in` and `ConstraintSystemchallenge_usable_after` are added for use cases that build PIOP sub-routine themselves, currently it supports up-to 3 phases as `{First,Second,Third}Phase`.

It allows us to allocate advice column in different interactive phases with extra challenges squeezed in-between. For example in `halo2_proofs/examples/shuffle.rs` it shows how to build a customized shuffle argument with such API.

### Unblinded advice column

`ConstraintSystem::unblinded_advice_column` is added for use cases that want to re-use advice column commitment among different proofs.

Worth mentioning, re-using advice column commitment in different proofs will need more blinding factors than the amount that prover adds, otherwise some information will be leaked and it's no longer perfect zero-knowledge.

## `Expression` extension

- `Expression::Challenge`

  A variant added for multi-phase. It can be obtained by `ConstraintSystemchallenge_usable_after` and used as a pseudo-random constant.

- `Expression::identifier`

  It prints `Expression` in a less verbose and human-readable way.

## `Circuit` extension

- `Circuit::Params`

  To use this, feature `circuit-params` needs to be turned on.

  A associated type added for configuring circuit with runtime parameter. 
  
  It allows us to implement `Circuit::params` to return the parameter of a circuit, and implement `Circuit::configure_with_params` to configure circuit with runtime parameter retrieved earlier.

## Proving & verifying key de/serialization and `SerdeFormat`

`ProvingKey::{read,write}` and `VerifyingKey::{read,write}` is added to serialize proving key and verifying key.

For field elements and elliptic curve points inside pk and vk, currently we have 3 different de/serialization format:

- `SerdeFormat::Processed`

  It de/serialize them as `PrimeField::Repr` and `GroupEncoding::Repr` respectively, and checks all elements are valid.

- `SerdeFormat::RawBytes`

  It de/serialize them as `SerdeObject::{from_raw_bytes,to_raw_bytes}` respectively, and checks all elements are valid.

- `SerdeFormat::RawBytesUnchecked`

  It de/serialize them as `SerdeObject::{from_raw_bytes,to_raw_bytes}` respectively, without checking if elements are valid.

Also `ParamsKZG::{read_custom,write_custom}` follows the same rule, and by default `ParamsKZG::{read,write}` uses `SerdeFormat::RawBytes` for efficiency.

## Thread safe `Region`

To use this, feature `thread-safe-region` needs to be turned on.

It constrains the `RegionLayouter` to be `Send` so we can have `Region` on different threads. It's useful when we want to arrange witness computation and assignment in the same place, but still keep the function `Send` so the caller can parallelize multiple of them.

## Optional selector compression

Currently `keygen_vk` changes configured `ConstraintSystem` to compresses simple selectors into smaller set of fixed columns to reduce cost.

For some use cases that want to keep configured `ConstraintSystem` unchanged they can do the verifying key generation by calling `keygen_vk_custom` with second argument as `false` instead, which disables the selector compression.

## `MockProver` improvement

- `MockProver::verify_par`

  Same checks as `MockProver::verify`, but parallelized.

- `MockProver::verify_at_rows`

  Same checks as `MockProver::verify`, but only on specified rows.

- `MockProver::verify_at_rows_par`

  Same checks as `MockProver::verify_at_rows`, but parallelized.

- `MockProver::assert_satisfied_par`

  Same assertions as `MockProver::assert_satisfied`, but parallelized.

- `MockProver::assert_satisfied_at_rows_par`

  Same assertions as `MockProver::assert_satisfied_par`, but only on specified rows.

## `Evaluator` and `evaluate_h`

They are introduced to improve quotient computation speed and memory usage for circuit with complicated `Expression`.
