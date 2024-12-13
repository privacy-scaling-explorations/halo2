use std::{collections::HashMap, iter};

use ff::{PrimeField, WithSmallOrderMulGroup};
use halo2curves::serde::SerdeObject;
use rand_chacha::ChaCha20Rng;
use rand_core::{RngCore, SeedableRng};

use super::Argument;
use crate::poly::commitment::{Params, PolynomialCommitmentScheme};
use crate::transcript::{Hashable, Transcript};
use crate::{
    utils::arithmetic::{eval_polynomial, parallelize},
    utils::multicore::current_num_threads,
    plonk::Error,
    poly::{Coeff, EvaluationDomain, ExtendedLagrangeCoeff, Polynomial, ProverQuery},
};

pub(in crate::plonk) struct Committed<F: PrimeField> {
    random_poly: Polynomial<F, Coeff>,
}

pub(in crate::plonk) struct Constructed<F: PrimeField> {
    h_pieces: Vec<Polynomial<F, Coeff>>,
    committed: Committed<F>,
}

pub(in crate::plonk) struct Evaluated<F: PrimeField> {
    h_pieces: Vec<Polynomial<F, Coeff>>,
    committed: Committed<F>,
}

impl<F: WithSmallOrderMulGroup<3>, CS: PolynomialCommitmentScheme<F>> Argument<F, CS> {
    pub(in crate::plonk) fn commit<R: RngCore, T: Transcript>(
        params: &CS::Parameters,
        domain: &EvaluationDomain<F>,
        mut rng: R,
        transcript: &mut T,
    ) -> Result<Committed<F>, Error>
    where
        CS::Commitment: Hashable<T::Hash> + SerdeObject,
        F: Hashable<T::Hash> + SerdeObject,
    {
        // Sample a random polynomial of degree n - 1
        let n = 1usize << domain.k() as usize;
        let mut rand_vec = vec![F::ZERO; n];

        let num_threads = current_num_threads();
        let chunk_size = n / num_threads;
        let thread_seeds = (0..)
            .step_by(chunk_size + 1)
            .take(n % num_threads)
            .chain(
                (chunk_size != 0)
                    .then(|| ((n % num_threads) * (chunk_size + 1)..).step_by(chunk_size))
                    .into_iter()
                    .flatten(),
            )
            .take(num_threads)
            .zip(iter::repeat_with(|| {
                let mut seed = [0u8; 32];
                rng.fill_bytes(&mut seed);
                ChaCha20Rng::from_seed(seed)
            }))
            .collect::<HashMap<_, _>>();

        parallelize(&mut rand_vec, |chunk, offset| {
            let mut rng = thread_seeds[&offset].clone();
            chunk.iter_mut().for_each(|v| *v = F::random(&mut rng));
        });

        let random_poly: Polynomial<F, Coeff> = domain.coeff_from_vec(rand_vec);

        // Commit
        let c = CS::commit(params, &random_poly);
        transcript.write(&c)?;

        Ok(Committed { random_poly })
    }
}

impl<F: WithSmallOrderMulGroup<3>> Committed<F> {
    pub(in crate::plonk) fn construct<CS: PolynomialCommitmentScheme<F>, T: Transcript>(
        self,
        params: &CS::Parameters,
        domain: &EvaluationDomain<F>,
        h_poly: Polynomial<F, ExtendedLagrangeCoeff>,
        transcript: &mut T,
    ) -> Result<Constructed<F>, Error>
    where
        CS::Commitment: Hashable<T::Hash> + SerdeObject,
        F: Hashable<T::Hash> + SerdeObject,
    {
        // Divide by t(X) = X^{params.n} - 1.
        let h_poly = domain.divide_by_vanishing_poly(h_poly);

        // Obtain final h(X) polynomial
        let h_poly = domain.extended_to_coeff(h_poly);

        // Split h(X) up into pieces
        let h_pieces = h_poly
            .chunks_exact(params.n() as usize)
            .map(|v| domain.coeff_from_vec(v.to_vec()))
            .collect::<Vec<_>>();
        drop(h_poly);

        // Compute commitments to each h(X) piece
        let h_commitments: Vec<_> = h_pieces
            .iter()
            .map(|h_piece| CS::commit(params, h_piece))
            .collect();

        // Hash each h(X) piece
        for c in h_commitments {
            transcript.write(&c)?;
        }

        Ok(Constructed {
            h_pieces,
            committed: self,
        })
    }
}

impl<F: PrimeField> Constructed<F> {
    pub(in crate::plonk) fn evaluate<T: Transcript>(
        self,
        x: F,
        transcript: &mut T,
    ) -> Result<Evaluated<F>, Error>
    where
        F: Hashable<T::Hash> + SerdeObject,
    {
        self.h_pieces.iter().try_for_each(|p| {
            let eval = eval_polynomial(p, x);
            transcript.write(&eval)
        })?;

        let random_eval = eval_polynomial(&self.committed.random_poly, x);
        transcript.write(&random_eval)?;

        Ok(Evaluated {
            h_pieces: self.h_pieces,
            committed: self.committed,
        })
    }
}

impl<F: PrimeField> Evaluated<F> {
    pub(in crate::plonk) fn open(&self, x: F) -> impl Iterator<Item = ProverQuery<'_, F>> + Clone {
        iter::empty()
            .chain(
                self.h_pieces
                    .iter()
                    .map(move |p| ProverQuery { point: x, poly: p }),
            )
            .chain(Some(ProverQuery {
                point: x,
                poly: &self.committed.random_poly,
            }))
    }
}
