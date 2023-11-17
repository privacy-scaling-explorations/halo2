#[cfg(test)]
mod test {
    use crate::arithmetic::eval_polynomial;
    use crate::plonk::Error;
    use crate::poly::commitment::Blind;
    use crate::poly::commitment::ParamsProver;
    use crate::poly::{
        commitment::{CommitmentScheme, Params, Prover, Verifier},
        query::{ProverQuery, VerifierQuery,CommitmentReference},
        strategy::VerificationStrategy,
        EvaluationDomain,
        Polynomial,
        Coeff
    };
    use crate::transcript::{
        Blake2bRead, Blake2bWrite, Challenge255, EncodedChallenge, Keccak256Read, Keccak256Write,
        TranscriptReadBuffer, TranscriptWriterBuffer,
    };
    use ff::WithSmallOrderMulGroup;
    use group::Curve;
    use rand_core::OsRng;

    #[test]
    fn test_roundtrip_ipa() {
        use crate::poly::ipa::commitment::{IPACommitmentScheme, ParamsIPA};
        use crate::poly::ipa::multiopen::{ProverIPA, VerifierIPA};
        use crate::poly::ipa::strategy::AccumulatorStrategy;
        use halo2curves::pasta::EqAffine;

        const K: u32 = 4;

        let params = ParamsIPA::<EqAffine>::new(K);

        let proof = create_proof::<
            IPACommitmentScheme<EqAffine>,
            ProverIPA<_>,
            _,
            Blake2bWrite<_, _, Challenge255<_>>,
        >(&params);

        let verifier_params = params.verifier_params();

        verify::<
            IPACommitmentScheme<EqAffine>,
            VerifierIPA<_>,
            _,
            Blake2bRead<_, _, Challenge255<_>>,
            AccumulatorStrategy<_>,
        >(verifier_params, &proof[..], false);

        verify::<
            IPACommitmentScheme<EqAffine>,
            VerifierIPA<_>,
            _,
            Blake2bRead<_, _, Challenge255<_>>,
            AccumulatorStrategy<_>,
        >(verifier_params, &proof[..], true);
    }

    #[test]
    fn test_roundtrip_ipa_keccak() {
        use crate::poly::ipa::commitment::{IPACommitmentScheme, ParamsIPA};
        use crate::poly::ipa::multiopen::{ProverIPA, VerifierIPA};
        use crate::poly::ipa::strategy::AccumulatorStrategy;
        use halo2curves::pasta::EqAffine;

        const K: u32 = 4;

        let params = ParamsIPA::<EqAffine>::new(K);

        let proof = create_proof::<
            IPACommitmentScheme<EqAffine>,
            ProverIPA<_>,
            _,
            Keccak256Write<_, _, Challenge255<_>>,
        >(&params);

        let verifier_params = params.verifier_params();

        verify::<
            IPACommitmentScheme<EqAffine>,
            VerifierIPA<_>,
            _,
            Keccak256Read<_, _, Challenge255<_>>,
            AccumulatorStrategy<_>,
        >(verifier_params, &proof[..], false);

        verify::<
            IPACommitmentScheme<EqAffine>,
            VerifierIPA<_>,
            _,
            Keccak256Read<_, _, Challenge255<_>>,
            AccumulatorStrategy<_>,
        >(verifier_params, &proof[..], true);
    }

    #[test]
    fn test_roundtrip_gwc() {
        use crate::poly::kzg::commitment::{KZGCommitmentScheme, ParamsKZG};
        use crate::poly::kzg::multiopen::{ProverGWC, VerifierGWC};
        use crate::poly::kzg::strategy::AccumulatorStrategy;
        use halo2curves::bn256::Bn256;

        const K: u32 = 4;

        let params = ParamsKZG::<Bn256>::new(K);

        let proof =
            create_proof::<_, ProverGWC<_>, _, Blake2bWrite<_, _, Challenge255<_>>>(&params);

        let verifier_params = params.verifier_params();

        verify::<_, VerifierGWC<_>, _, Blake2bRead<_, _, Challenge255<_>>, AccumulatorStrategy<_>>(
            verifier_params,
            &proof[..],
            false,
        );

        verify::<
            KZGCommitmentScheme<Bn256>,
            VerifierGWC<_>,
            _,
            Blake2bRead<_, _, Challenge255<_>>,
            AccumulatorStrategy<_>,
        >(verifier_params, &proof[..], true);
    }

    #[test]
    fn test_roundtrip_shplonk() {
        use crate::poly::kzg::commitment::{KZGCommitmentScheme, ParamsKZG};
        use crate::poly::kzg::multiopen::{ProverSHPLONK, VerifierSHPLONK};
        use crate::poly::kzg::strategy::AccumulatorStrategy;
        use halo2curves::bn256::Bn256;

        const K: u32 = 4;

        let params = ParamsKZG::<Bn256>::new(K);

        let proof = create_proof::<
            KZGCommitmentScheme<Bn256>,
            ProverSHPLONK<_>,
            _,
            Blake2bWrite<_, _, Challenge255<_>>,
        >(&params);

        let verifier_params = params.verifier_params();

        verify::<
            KZGCommitmentScheme<Bn256>,
            VerifierSHPLONK<_>,
            _,
            Blake2bRead<_, _, Challenge255<_>>,
            AccumulatorStrategy<_>,
        >(verifier_params, &proof[..], false);

        verify::<
            KZGCommitmentScheme<Bn256>,
            VerifierSHPLONK<_>,
            _,
            Blake2bRead<_, _, Challenge255<_>>,
            AccumulatorStrategy<_>,
        >(verifier_params, &proof[..], true);
    }

    fn verify<
        'a,
        'params,
        Scheme: CommitmentScheme,
        V: Verifier<'params, Scheme>,
        E: EncodedChallenge<Scheme::Curve>,
        T: TranscriptReadBuffer<&'a [u8], Scheme::Curve, E>,
        Strategy: VerificationStrategy<'params, Scheme, V, Output = Strategy>,
    >(
        params: &'params Scheme::ParamsVerifier,
        proof: &'a [u8],
        should_fail: bool,
    ) {
        let verifier = V::new(params);

        let mut transcript = T::init(proof);

        let a = transcript.read_point().unwrap();
        let b = transcript.read_point().unwrap();
        let c = transcript.read_point().unwrap();

        let x = transcript.squeeze_challenge();
        let y = transcript.squeeze_challenge();

        let avx = transcript.read_scalar().unwrap();
        let bvx = transcript.read_scalar().unwrap();
        let cvy = transcript.read_scalar().unwrap();

        let valid_queries = std::iter::empty()
            .chain(Some(VerifierQuery::new_commitment(&a, x.get_scalar(), avx)))
            .chain(Some(VerifierQuery::new_commitment(&b, x.get_scalar(), bvx)))
            .chain(Some(VerifierQuery::new_commitment(&c, y.get_scalar(), cvy)));

        let invalid_queries = std::iter::empty()
            .chain(Some(VerifierQuery::new_commitment(&a, x.get_scalar(), avx)))
            .chain(Some(VerifierQuery::new_commitment(&b, x.get_scalar(), avx)))
            .chain(Some(VerifierQuery::new_commitment(&c, y.get_scalar(), cvy)));

        let queries = if should_fail {
            invalid_queries.clone()
        } else {
            valid_queries.clone()
        };

        {
            let strategy = Strategy::new(params);
            let strategy = strategy
                .process(|msm_accumulator| {
                    verifier
                        .verify_proof(&mut transcript, queries.clone(), msm_accumulator)
                        .map_err(|_| Error::Opening)
                })
                .unwrap();

            assert_eq!(strategy.finalize(), !should_fail);
        }
    }

    fn create_proof<
        'params,
        Scheme: CommitmentScheme,
        P: Prover<'params, Scheme>,
        E: EncodedChallenge<Scheme::Curve>,
        T: TranscriptWriterBuffer<Vec<u8>, Scheme::Curve, E>,
    >(
        params: &'params Scheme::ParamsProver,
    ) -> Vec<u8>
    where
        Scheme::Scalar: WithSmallOrderMulGroup<3>,
    {
        let domain = EvaluationDomain::new(1, params.k());

        let mut ax = domain.empty_coeff();
        for (i, a) in ax.iter_mut().enumerate() {
            *a = <<Scheme as CommitmentScheme>::Scalar>::from(10 + i as u64);
        }

        let mut bx = domain.empty_coeff();
        for (i, a) in bx.iter_mut().enumerate() {
            *a = <<Scheme as CommitmentScheme>::Scalar>::from(100 + i as u64);
        }

        let mut cx = domain.empty_coeff();
        for (i, a) in cx.iter_mut().enumerate() {
            *a = <<Scheme as CommitmentScheme>::Scalar>::from(100 + i as u64);
        }

        let mut transcript = T::init(vec![]);

        let blind = Blind::new(&mut OsRng);
        let a = params.commit(&ax, blind).to_affine();
        let b = params.commit(&bx, blind).to_affine();
        let c = params.commit(&cx, blind).to_affine();

        transcript.write_point(a).unwrap();
        transcript.write_point(b).unwrap();
        transcript.write_point(c).unwrap();

        let x = transcript.squeeze_challenge();
        let y = transcript.squeeze_challenge();

        let avx = eval_polynomial(&ax, x.get_scalar());
        let bvx = eval_polynomial(&bx, x.get_scalar());
        let cvy = eval_polynomial(&cx, y.get_scalar());

        transcript.write_scalar(avx).unwrap();
        transcript.write_scalar(bvx).unwrap();
        transcript.write_scalar(cvy).unwrap();

        let queries = [
            ProverQuery {
                point: x.get_scalar(),
                poly: &ax,
                blind,
            },
            ProverQuery {
                point: x.get_scalar(),
                poly: &bx,
                blind,
            },
            ProverQuery {
                point: y.get_scalar(),
                poly: &cx,
                blind,
            },
        ]
        .to_vec();

        let prover = P::new(params);
        prover
            .create_proof(&mut OsRng, &mut transcript, queries)
            .unwrap();

        transcript.finalize()
    }


     fn create_proof_sh_plonk<
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
        commitment_list:Vec<Scheme::Curve>,
    ) -> Vec<u8>
    where
        Scheme::Scalar: WithSmallOrderMulGroup<3>,
    {
        assert!(points_list.len()==polynomial_list.len());
        assert!(points_list.len()==commitment_list.len());
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
            let temp=ProverQuery::new_query(
                points_list[i], &polynomial_list[i],blind
            );
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
    fn verify_shplonk<
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
        for i in 0..points_list.len() {
            let temp = transcript.read_point().unwrap();
            commitment_list.push(temp);
        }
        // read the point list from transcript
        let mut polynomial_list = Vec::new();
        for i in 0..points_list.len() {
            let temp: Scheme::Scalar = transcript.read_scalar().unwrap();
            polynomial_list.push(temp);
        }
        // add the queries
        let mut queries = Vec::new();
        for i in 0..points_list.len() {
            let temp =  VerifierQuery::new_commitment(
                &commitment_list[i],
                points_list[i],
                polynomial_list[i]);

            queries.push(temp);
        }
        // now, we apply the verify function from SHPLONK to return the result
        let strategy = Strategy::new(params);
        let strategy = strategy
            .process(|msm_accumulator| {
                verifier
                    .verify_proof(&mut transcript, queries.clone(), msm_accumulator)
                    .map_err(|_| Error::Opening)
            })
            .unwrap();

        strategy.finalize()
    }



}
