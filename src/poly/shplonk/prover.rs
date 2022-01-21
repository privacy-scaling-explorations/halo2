use super::super::{
    commitment::{self, Blind, Params},
    Coeff, Polynomial,
};
use super::{
    construct_intermediate_sets, ChallengeU, ChallengeV, CommitmentData, ProverQuery, Query,
};

use crate::arithmetic::{
    eval_polynomial, kate_division, lagrange_interpolate, vanishing_polynomial, CurveAffine,
    FieldExt,
};
use crate::transcript::{EncodedChallenge, TranscriptWrite};

use ff::Field;
use group::Curve;
use rand::RngCore;
use std::io;
use std::marker::PhantomData;

/// Create a multi-opening proof
pub fn create_proof<'a, I, C: CurveAffine, E: EncodedChallenge<C>, T: TranscriptWrite<C, E>>(
    params: &Params<C>,
    transcript: &mut T,
    queries: I,
) -> io::Result<()>
where
    I: IntoIterator<Item = ProverQuery<'a, C>> + Clone,
{
    let v: ChallengeV<_> = transcript.squeeze_challenge_scalar();

    let zero = || Polynomial::<C::Scalar, Coeff> {
        values: vec![C::Scalar::zero(); params.n as usize],
        _marker: PhantomData,
    };

    let (commitment_data, all_points) = construct_intermediate_sets(queries);

    let calculate_low_degree_equivalent =
        |points: &[C::Scalar], evals: &[C::Scalar]| -> Polynomial<C::Scalar, Coeff> {
            let mut poly = lagrange_interpolate(points, evals);
            poly.resize(params.n as usize, C::Scalar::zero());

            Polynomial {
                values: poly,
                _marker: PhantomData,
            }
        };

    let div_by_vanising =
        |poly: Polynomial<C::Scalar, Coeff>, roots: &[C::Scalar]| -> Polynomial<C::Scalar, Coeff> {
            let num_coeffs_0 = poly.num_coeffs();

            let mut poly = roots
                .iter()
                .fold(poly.values, |poly, point| kate_division(&poly, *point));

            let num_coeffs_1 = poly.len();
            // sanity check
            // expect perfect division
            assert_eq!(num_coeffs_0, num_coeffs_1 + roots.len());

            poly.resize(params.n as usize, C::Scalar::zero());
            Polynomial {
                values: poly,
                _marker: PhantomData,
            }
        };

    let low_degree_equivalent_polynomials: Vec<Polynomial<C::Scalar, Coeff>> = commitment_data
        .iter()
        .map(|commitment_data| {
            let queries = &commitment_data.points;

            let evals: Vec<C::Scalar> = queries.iter().map(|(_, eval)| *eval).collect();
            let points: Vec<_> = queries
                .iter()
                .map(|(evaluation_point, _)| *evaluation_point)
                .collect();

            calculate_low_degree_equivalent(&points[..], &evals[..])
        })
        .collect();

    let quotient_polynomials: Vec<Polynomial<C::Scalar, Coeff>> = commitment_data
        .iter()
        .zip(low_degree_equivalent_polynomials.iter())
        .map(|(commitment_data, low_degree_equivalent)| {
            let points: Vec<_> = commitment_data
                .points
                .iter()
                .map(|(evaluation_point, _)| *evaluation_point)
                .collect();
            let poly: Polynomial<C::Scalar, Coeff> = commitment_data.commitment.poly.clone();

            let numerator_poly = poly - low_degree_equivalent;
            div_by_vanising(numerator_poly, &points[..])
        })
        .collect();

    let h_x: Polynomial<C::Scalar, Coeff> = quotient_polynomials
        .iter()
        .fold(zero(), |acc, q_x| (acc * *v) + q_x);

    let h = params.commit(&h_x).to_affine();
    transcript.write_point(h)?;
    let u: ChallengeU<_> = transcript.squeeze_challenge_scalar();

    let zt_x = vanishing_polynomial(&all_points[..]);
    let zt_eval = eval_polynomial(&zt_x[..], *u);

    let linearisation_contribs: Vec<Polynomial<C::Scalar, Coeff>> = commitment_data
        .iter()
        .zip(low_degree_equivalent_polynomials.iter())
        .map(|(commitment_data, low_degree_equivalent)| {
            let z_diff = vanishing_polynomial(&commitment_data.diffs[..]);
            let z_i = eval_polynomial(&z_diff[..], *u);
            (commitment_data.commitment.poly - eval_polynomial(low_degree_equivalent, *u)) * z_i
        })
        .collect();

    let l_x: Polynomial<C::Scalar, Coeff> = linearisation_contribs
        .iter()
        .fold(zero(), |acc, q_x| (acc * *v) + q_x);

    let l_x = l_x - &(h_x * zt_eval);

    // sanity check
    {
        let must_be_zero = eval_polynomial(&l_x.values[..], *u);
        assert_eq!(must_be_zero, C::Scalar::zero());
    }

    let h_x = Polynomial {
        values: kate_division(&l_x.values, *u),
        _marker: PhantomData,
    };

    let h = params.commit(&h_x).to_affine();
    transcript.write_point(h)?;

    Ok(())
}

#[doc(hidden)]
#[derive(Copy, Clone)]
pub struct PolynomialPointer<'a, C: CurveAffine> {
    poly: &'a Polynomial<C::Scalar, Coeff>,
}

impl<'a, C: CurveAffine> PartialEq for PolynomialPointer<'a, C> {
    fn eq(&self, other: &Self) -> bool {
        std::ptr::eq(self.poly, other.poly)
    }
}

impl<'a, C: CurveAffine> Query<C::Scalar> for ProverQuery<'a, C> {
    type Commitment = PolynomialPointer<'a, C>;

    fn get_point(&self) -> C::Scalar {
        self.point
    }
    fn get_eval(&self) -> C::Scalar {
        eval_polynomial(self.poly, self.point)
    }
    fn get_commitment(&self) -> Self::Commitment {
        PolynomialPointer { poly: self.poly }
    }
}
