use super::{
    query::{ProverQuery, VerifierQuery},
    strategy::Guard,
    Coeff, LagrangeCoeff, Polynomial,
};
use crate::arithmetic::eval_polynomial;
use crate::plonk::Error as Err;
use crate::poly::{Error, VerificationStrategy};
use crate::transcript::{
    EncodedChallenge, TranscriptRead, TranscriptReadBuffer, TranscriptWrite, TranscriptWriterBuffer,
};
use ff::Field;
use ff::WithSmallOrderMulGroup;
use halo2curves::CurveAffine;
use rand_core::OsRng;
use rand_core::RngCore;
use std::{
    fmt::Debug,
    io::{self},
    ops::{Add, AddAssign, Mul, MulAssign},
};
/// Defines components of a commitment scheme.
pub trait CommitmentScheme {
    /// Application field of this commitment scheme
    type Scalar: Field;

    /// Elliptic curve used to commit the application and witnesses
    type Curve: CurveAffine<ScalarExt = Self::Scalar>;

    /// Constant prover parameters
    type ParamsProver: for<'params> ParamsProver<
        'params,
        Self::Curve,
        ParamsVerifier = Self::ParamsVerifier,
    >;

    /// Constant verifier parameters
    type ParamsVerifier: for<'params> ParamsVerifier<'params, Self::Curve>;

    /// Wrapper for parameter generator
    fn new_params(k: u32) -> Self::ParamsProver;

    /// Wrapper for parameter reader
    fn read_params<R: io::Read>(reader: &mut R) -> io::Result<Self::ParamsProver>;
}

/// Parameters for circuit sysnthesis and prover parameters.
pub trait Params<'params, C: CurveAffine>: Sized + Clone {
    /// Multi scalar multiplication engine
    type MSM: MSM<C> + 'params;

    /// Logaritmic size of the circuit
    fn k(&self) -> u32;

    /// Size of the circuit
    fn n(&self) -> u64;

    /// Downsize `Params` with smaller `k`.
    fn downsize(&mut self, k: u32);

    /// Generates an empty multiscalar multiplication struct using the
    /// appropriate params.
    fn empty_msm(&'params self) -> Self::MSM;

    /// This commits to a polynomial using its evaluations over the $2^k$ size
    /// evaluation domain. The commitment will be blinded by the blinding factor
    /// `r`.
    fn commit_lagrange(
        &self,
        poly: &Polynomial<C::ScalarExt, LagrangeCoeff>,
        r: Blind<C::ScalarExt>,
    ) -> C::CurveExt;

    /// Writes params to a buffer.
    fn write<W: io::Write>(&self, writer: &mut W) -> io::Result<()>;

    /// Reads params from a buffer.
    fn read<R: io::Read>(reader: &mut R) -> io::Result<Self>;
}

/// Parameters for circuit sysnthesis and prover parameters.
pub trait ParamsProver<'params, C: CurveAffine>: Params<'params, C> {
    /// Constant verifier parameters.
    type ParamsVerifier: ParamsVerifier<'params, C>;

    /// Returns new instance of parameters
    fn new(k: u32) -> Self;

    /// This computes a commitment to a polynomial described by the provided
    /// slice of coefficients. The commitment may be blinded by the blinding
    /// factor `r`.
    fn commit(&self, poly: &Polynomial<C::ScalarExt, Coeff>, r: Blind<C::ScalarExt>)
        -> C::CurveExt;

    /// Getter for g generators
    fn get_g(&self) -> &[C];

    /// Returns verification parameters.
    fn verifier_params(&'params self) -> &'params Self::ParamsVerifier;
}

/// Verifier specific functionality with circuit constraints
pub trait ParamsVerifier<'params, C: CurveAffine>: Params<'params, C> {}

/// Multi scalar multiplication engine
pub trait MSM<C: CurveAffine>: Clone + Debug + Send + Sync {
    /// Add arbitrary term (the scalar and the point)
    fn append_term(&mut self, scalar: C::Scalar, point: C::CurveExt);

    /// Add another multiexp into this one
    fn add_msm(&mut self, other: &Self)
    where
        Self: Sized;

    /// Scale all scalars in the MSM by some scaling factor
    fn scale(&mut self, factor: C::Scalar);

    /// Perform multiexp and check that it results in zero
    fn check(&self) -> bool;

    /// Perform multiexp and return the result
    fn eval(&self) -> C::CurveExt;

    /// Return base points
    fn bases(&self) -> Vec<C::CurveExt>;

    /// Scalars
    fn scalars(&self) -> Vec<C::Scalar>;
}

/// Common multi-open prover interface for various commitment schemes
pub trait Prover<'params, Scheme: CommitmentScheme> {
    /// Query instance or not
    const QUERY_INSTANCE: bool;

    /// Creates new prover instance
    fn new(params: &'params Scheme::ParamsProver) -> Self;

    /// Create a multi-opening proof
    fn create_proof<
        'com,
        E: EncodedChallenge<Scheme::Curve>,
        T: TranscriptWrite<Scheme::Curve, E>,
        R,
        I,
    >(
        &self,
        rng: R,
        transcript: &mut T,
        queries: I,
    ) -> io::Result<()>
    where
        I: IntoIterator<Item = ProverQuery<'com, Scheme::Curve>> + Clone,
        R: RngCore;
}

/// Common multi-open verifier interface for various commitment schemes
pub trait Verifier<'params, Scheme: CommitmentScheme> {
    /// Unfinalized verification result. This is returned in verification
    /// to allow developer to compress or combined verification results
    type Guard: Guard<Scheme, MSMAccumulator = Self::MSMAccumulator>;

    /// Accumulator fot comressed verification
    type MSMAccumulator;

    /// Query instance or not
    const QUERY_INSTANCE: bool;

    /// Creates new verifier instance
    fn new(params: &'params Scheme::ParamsVerifier) -> Self;

    /// Process the proof and returns unfinished result named `Guard`
    fn verify_proof<
        'com,
        E: EncodedChallenge<Scheme::Curve>,
        T: TranscriptRead<Scheme::Curve, E>,
        I,
    >(
        &self,
        transcript: &mut T,
        queries: I,
        msm: Self::MSMAccumulator,
    ) -> Result<Self::Guard, Error>
    where
        'params: 'com,
        I: IntoIterator<
                Item = VerifierQuery<
                    'com,
                    Scheme::Curve,
                    <Scheme::ParamsVerifier as Params<'params, Scheme::Curve>>::MSM,
                >,
            > + Clone;
}

fn friendly_create_proof<
    'params,
    Scheme: CommitmentScheme,
    P: Prover<'params, Scheme>,
    E: EncodedChallenge<Scheme::Curve>,
    TW: TranscriptWriterBuffer<Vec<u8>, Scheme::Curve, E>,
>(
    params: &'params Scheme::ParamsProver,
    // a list of point x_1,x_2,...x_n
    points_list: Vec<Scheme::Scalar>,
    // a list of polynomials p_1(x), p_2(x),...,p_n(x)
    polynomial_list: Vec<Polynomial<Scheme::Scalar, Coeff>>,
    // the list of commitment of p_1(x),p_2(x),...,p_n(x)
    commitment_list: Vec<Scheme::Curve>,
) -> Vec<u8>
where
    Scheme::Scalar: WithSmallOrderMulGroup<3>,
{
    assert!(points_list.len() == polynomial_list.len());
    assert!(points_list.len() == commitment_list.len());
    // this function, given a list of points x_1,x_2,...,x_n
    // and polynomials p_1(x),p_2(x),...,p_n(x)
    // create a witness for the value p_1(x_1), p_2(x_2),...,p_n(x_n)
    let mut transcript = TW::init(Vec::new());

    let blind = Blind::new(&mut OsRng);
    // Add the commitment the polynomial p_i(x) to transcript
    for i in 0..polynomial_list.len() {
        transcript.write_point(commitment_list[i]).unwrap();
    }
    // evaluate the values p_i(x_i) for i=1,2,...,n
    for i in 0..polynomial_list.len() {
        let av = eval_polynomial(&polynomial_list[i], points_list[i]);
        transcript.write_scalar(av).unwrap();
    }

    // this query is used to list all the values p_1(x_1), p_2(x_2),...,p_n(x_n)
    // in the query list of shplonk prover

    let mut queries: Vec<ProverQuery<'_, <Scheme as CommitmentScheme>::Curve>> = Vec::new();
    for i in 0..polynomial_list.len() {
        let temp = ProverQuery {
            point: points_list[i],
            poly: &polynomial_list[i],
            blind: blind,
        };
        queries.push(temp);
    }
    // create the proof
    let prover = P::new(params);
    prover
        .create_proof(&mut OsRng, &mut transcript, queries)
        .unwrap();

    transcript.finalize()
}

//Verify KZG openings
// Used to create a friendly KZG API verification function
fn friendly_verify<
    'a,
    'params,
    Scheme: CommitmentScheme,
    Vr: Verifier<'params, Scheme>,
    E: EncodedChallenge<Scheme::Curve>,
    Tr: TranscriptReadBuffer<&'a [u8], Scheme::Curve, E>,
    Strategy: VerificationStrategy<'params, Scheme, Vr, Output = Strategy>,
>(
    params: &'params Scheme::ParamsVerifier,
    // // a list of point x_1,x_2,...x_n
    points_list: Vec<Scheme::Scalar>,
    // the proof of opening
    proof: &'a [u8],
) -> bool {
    let verifier = Vr::new(params);

    let mut transcript = Tr::init(proof);
    // read commitment list from transcript
    let mut commitment_list = Vec::new();
    for _i in 0..points_list.len() {
        let temp = transcript.read_point().unwrap();
        commitment_list.push(temp);
    }
    // read the point list from transcript
    let mut polynomial_list = Vec::new();
    for _i in 0..points_list.len() {
        let temp: Scheme::Scalar = transcript.read_scalar().unwrap();
        polynomial_list.push(temp);
    }
    // add the queries
    let mut queries = Vec::new();
    for i in 0..points_list.len() {
        let temp =
            VerifierQuery::new_commitment(&commitment_list[i], points_list[i], polynomial_list[i]);

        queries.push(temp);
    }
    // now, we apply the verify function from SHPLONK to return the result
    let strategy = Strategy::new(params);
    let strategy = strategy
        .process(|msm_accumulator| {
            verifier
                .verify_proof(&mut transcript, queries.clone(), msm_accumulator)
                .map_err(|_| Err::Opening)
        })
        .unwrap();

    strategy.finalize()
}

/// Wrapper type around a blinding factor.
#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub struct Blind<F>(pub F);

impl<F: Field> Default for Blind<F> {
    fn default() -> Self {
        Blind(F::ONE)
    }
}

impl<F: Field> Blind<F> {
    /// Given `rng` creates new blinding scalar
    pub fn new<R: RngCore>(rng: &mut R) -> Self {
        Blind(F::random(rng))
    }
}

impl<F: Field> Add for Blind<F> {
    type Output = Self;

    fn add(self, rhs: Blind<F>) -> Self {
        Blind(self.0 + rhs.0)
    }
}

impl<F: Field> Mul for Blind<F> {
    type Output = Self;

    fn mul(self, rhs: Blind<F>) -> Self {
        Blind(self.0 * rhs.0)
    }
}

impl<F: Field> AddAssign for Blind<F> {
    fn add_assign(&mut self, rhs: Blind<F>) {
        self.0 += rhs.0;
    }
}

impl<F: Field> MulAssign for Blind<F> {
    fn mul_assign(&mut self, rhs: Blind<F>) {
        self.0 *= rhs.0;
    }
}

impl<F: Field> AddAssign<F> for Blind<F> {
    fn add_assign(&mut self, rhs: F) {
        self.0 += rhs;
    }
}

impl<F: Field> MulAssign<F> for Blind<F> {
    fn mul_assign(&mut self, rhs: F) {
        self.0 *= rhs;
    }
}
