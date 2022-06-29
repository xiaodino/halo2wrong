use crate::spec::Poseidon;
use halo2::arithmetic::FieldExt;
use maingate::halo2::plonk::Error;
use maingate::MainGateInstructions;
use maingate::{halo2, AssignedValue, RegionCtx, Term};
use maingate::{MainGate, MainGateConfig};
use std::iter;

#[derive(Clone, Debug)]
pub struct PoseidonChip<
    F: FieldExt,
    const RF: usize,
    const RP: usize,
    const T: usize,
    const RATE: usize,
> {
    pub(crate) main_gate_config: MainGateConfig,
    pub(crate) spec: Poseidon<F, RF, RP, T, RATE>,
}

impl<F: FieldExt, const RF: usize, const RP: usize, const T: usize, const RATE: usize>
    PoseidonChip<F, RF, RP, T, RATE>
{
    fn main_gate(&self) -> MainGate<F> {
        MainGate::<F>::new(self.main_gate_config.clone())
    }
}

pub trait PoseidonInstructions<F: FieldExt, const RATE: usize> {
    fn hash(
        &self,

        ctx: &mut RegionCtx<'_, '_, F>,
        inputs: &[AssignedValue<F>; RATE],
    ) -> Result<AssignedValue<F>, Error>;
}

impl<F: FieldExt, const RF: usize, const RP: usize, const T: usize, const RATE: usize>
    PoseidonInstructions<F, RATE> for PoseidonChip<F, RF, RP, T, RATE>
{
    fn hash(
        &self,

        ctx: &mut RegionCtx<'_, '_, F>,
        inputs: &[AssignedValue<F>; RATE],
    ) -> Result<AssignedValue<F>, Error> {
        let main_gate = self.main_gate();
        let capacity_value = F::from_u128(1 << (T - 1));

        let state: &mut [AssignedValue<F>; T] = &mut iter::empty()
            .chain(main_gate.assign_constant(ctx, capacity_value))
            .chain(inputs.to_vec())
            .collect::<Vec<AssignedValue<F>>>()
            .try_into()
            .unwrap();

        for round_number in 0..(RF / 2) {
            self.add_round_constants(ctx, round_number, state)?;
            self.sbox_full(ctx, state)?;
            self.apply_mds_matrix(ctx, state)?;
        }

        for round_number in (RF / 2)..(RF / 2 + RP) {
            self.add_round_constants(ctx, round_number, state)?;
            self.sbox_partial(ctx, state)?;
            self.apply_mds_matrix(ctx, state)?;
        }

        for round_number in (RF / 2 + RP)..(RF + RP) {
            self.add_round_constants(ctx, round_number, state)?;
            self.sbox_full(ctx, state)?;
            self.apply_mds_matrix(ctx, state)?;
        }

        Ok(state[1])
    }
}

impl<F: FieldExt, const RF: usize, const RP: usize, const T: usize, const RATE: usize>
    PoseidonChip<F, RF, RP, T, RATE>
{
    // Add round constants
    fn add_round_constants(
        &self,

        ctx: &mut RegionCtx<'_, '_, F>,
        round_number: usize,
        state: &mut [AssignedValue<F>; T],
    ) -> Result<(), Error> {
        let main_gate = self.main_gate();

        assert!(round_number < RF + RP);

        let round_constants = self.spec.round_constants[round_number];
        for (word, round_constant) in state.iter_mut().zip(round_constants.into_iter()) {
            *word = main_gate.add_constant(ctx, &word, round_constant)?;
        }
        Ok(())
    }

    // Applies full sbox
    fn sbox_full(
        &self,

        ctx: &mut RegionCtx<'_, '_, F>,
        state: &mut [AssignedValue<F>; T],
    ) -> Result<(), Error> {
        let main_gate = self.main_gate();
        for word in state.iter_mut() {
            let t = main_gate.mul(ctx, word, word)?;
            let t = main_gate.mul(ctx, &t, &t)?;
            *word = main_gate.mul(ctx, &t, word)?;
        }
        Ok(())
    }

    // Applies partial sbox
    fn sbox_partial(
        &self,

        ctx: &mut RegionCtx<'_, '_, F>,
        state: &mut [AssignedValue<F>; T],
    ) -> Result<(), Error> {
        let main_gate = self.main_gate();

        let t = main_gate.mul(ctx, &state[0], &state[0])?;
        let t = main_gate.mul(ctx, &t, &t)?;
        state[0] = main_gate.mul(ctx, &t, &state[0])?;

        Ok(())
    }

    // Applies partial sbox
    fn apply_mds_matrix(
        &self,

        ctx: &mut RegionCtx<'_, '_, F>,
        state: &mut [AssignedValue<F>; T],
    ) -> Result<(), Error> {
        let main_gate = self.main_gate();
        let mds = self.spec.mds;

        let new_state = mds
            .iter()
            .map(|row| {
                // term_i = s_0 * e_i_0 + s_1 * e_i_1 + ....
                let terms: Vec<Term<F>> = state
                    .iter()
                    .zip(row.iter())
                    .map(|(word, e)| Term::Assigned(*word, *e))
                    .collect();

                main_gate.compose(ctx, &terms[..], F::zero())
            })
            .collect::<Result<Vec<AssignedValue<F>>, Error>>()?;

        for (word, new_word) in state.iter_mut().zip(new_state.iter()) {
            *word = *new_word
        }

        Ok(())
    }
}

#[cfg(test)]
mod test {

    use crate::spec::Poseidon;

    use halo2::arithmetic::FieldExt;
    use halo2::circuit::Layouter;
    use halo2::circuit::SimpleFloorPlanner;
    use halo2::dev::MockProver;
    use halo2::plonk::keygen_vk;
    use halo2::plonk::Error;
    use halo2::plonk::{Circuit, ConstraintSystem};
    use halo2::poly::commitment::ParamsProver;
    use halo2::transcript::{
        Blake2bRead, Blake2bWrite, Challenge255, TranscriptReadBuffer, TranscriptWriterBuffer,
    };

    use maingate::halo2;
    use maingate::halo2::halo2curves;
    use maingate::halo2::plonk::create_proof;
    use maingate::halo2::plonk::keygen_pk;
    use maingate::halo2::plonk::verify_proof;
    use maingate::AssignedValue;
    use maingate::MainGate;
    use maingate::MainGateConfig;
    use maingate::{MainGateInstructions, RegionCtx};

    use poseidon::merkle::Poseidon as Reference;

    use rand_core::OsRng;

    use super::PoseidonChip;
    use super::PoseidonInstructions;

    use crate::spec::*;

    #[derive(Clone)]
    struct TestConfig {
        main_gate_config: MainGateConfig,
    }

    impl TestConfig {
        fn new<F: FieldExt>(meta: &mut ConstraintSystem<F>) -> Self {
            let main_gate_config = MainGate::<F>::configure(meta);

            TestConfig { main_gate_config }
        }
    }

    #[derive(Clone)]
    struct TestCircuit<F: FieldExt> {
        left: Option<F>,
        right: Option<F>,
        top: Option<F>,
        poseidon_spec: Poseidon<F, RF, RP, T, RATE>,
    }

    impl<F: FieldExt> TestCircuit<F> {
        fn poseidon_chip(
            &self,
            main_gate_config: MainGateConfig,
        ) -> PoseidonChip<F, RF, RP, T, RATE> {
            PoseidonChip {
                spec: self.poseidon_spec.clone(),
                main_gate_config,
            }
        }
    }

    impl<F: FieldExt> Circuit<F> for TestCircuit<F> {
        type Config = TestConfig;
        type FloorPlanner = SimpleFloorPlanner;

        fn without_witnesses(&self) -> Self {
            unimplemented!();
        }

        fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
            TestConfig::new::<F>(meta)
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<F>,
        ) -> Result<(), Error> {
            let main_gate = MainGate::<F>::new(config.main_gate_config.clone());
            let poseidon_chip = self.poseidon_chip(config.main_gate_config.clone());

            let (top, right) = layouter.assign_region(
                // layouter.assign_region(
                || "some region",
                |mut region| {
                    let offset = &mut 0;
                    let ctx = &mut RegionCtx::new(&mut region, offset);

                    let left = main_gate.assign_value(ctx, &self.left.into())?;
                    let right = main_gate.assign_value(ctx, &self.right.into())?;
                    let assigned_inputs: &mut [AssignedValue<F>; 2] = &mut [left, right];
                    let top_0 = poseidon_chip.hash(ctx, assigned_inputs)?;

                    let top_1 = main_gate.assign_value(ctx, &self.top.into())?;

                    main_gate.assert_equal(ctx, &top_0, &top_1)?;

                    Ok((top_1, right))
                },
            )?;

            main_gate.expose_public(layouter.namespace(|| "right"), right, 0)?;
            main_gate.expose_public(layouter.namespace(|| "top"), top, 1)?;

            Ok(())
        }
    }

    #[test]
    fn test_mock() {
        use halo2curves::bn256::Fr;

        const K: u32 = 12;

        let left = Fr::from(0);
        let right = Fr::from(1);
        let ref_hasher = Reference::<Fr, T, RATE>::new(RF, RP);
        let top = ref_hasher.hash(&[left, right].try_into().unwrap());

        let circuit = TestCircuit {
            left: Some(left),
            right: Some(right),
            top: Some(top),
            poseidon_spec: bn_poseidon_8_55_3_2(),
        };

        let public_inputs = vec![vec![right, top]];
        let prover = match MockProver::run(K, &circuit, public_inputs) {
            Ok(prover) => prover,
            Err(e) => panic!("{:#?}", e),
        };
        assert_eq!(prover.verify(), Ok(()));
    }

    #[test]
    fn test_kzg() {
        use halo2curves::bn256::{Fr, G1Affine};

        use halo2::poly::kzg::commitment::{KZGCommitmentScheme, ParamsKZG};
        use halo2::poly::kzg::multiopen::{ProverSHPLONK, VerifierSHPLONK};
        use halo2::poly::kzg::strategy::BatchVerifier;
        use halo2curves::bn256::Bn256;

        type Scheme = KZGCommitmentScheme<Bn256>;
        type Prover<'a> = ProverSHPLONK<'a, Bn256>;
        type Verifier<'a> = VerifierSHPLONK<'a, Bn256>;

        const K: u32 = 14;
        let params = ParamsKZG::<Bn256>::new(K);
        let verifier_params = params.verifier_params();
        let rng = OsRng;

        let left = Fr::from(0);
        let right = Fr::from(1);
        let ref_hasher = Reference::<Fr, T, RATE>::new(RF, RP);
        let top = ref_hasher.hash(&[left, right].try_into().unwrap());

        // Synthesis

        let circuit = TestCircuit {
            left: None,
            right: None,
            top: None,
            poseidon_spec: bn_poseidon_8_55_3_2(),
        };

        let verifier_key =
            keygen_vk::<Scheme, _>(&params, &circuit).expect("keygen_vk should not fail");
        let prover_key = keygen_pk::<Scheme, _>(&params, verifier_key.clone(), &circuit)
            .expect("keygen_pk should not fail");

        // Prover

        let circuit = TestCircuit {
            left: Some(left),
            right: Some(right),
            top: Some(top),
            poseidon_spec: bn_poseidon_8_55_3_2(),
        };

        let mut transcript = Blake2bWrite::<Vec<u8>, G1Affine, Challenge255<_>>::init(vec![]);
        create_proof::<_, Prover, _, _, _, _>(
            &params,
            &prover_key,
            &[circuit.clone()],
            &[&[&[right, top]]],
            rng,
            &mut transcript,
        )
        .expect("proof to be returned");
        let proof = transcript.finalize();

        // Verifier

        let mut transcript = Blake2bRead::<&[u8], G1Affine, Challenge255<_>>::init(&proof);
        let strategy = BatchVerifier::new(&params, OsRng);

        use halo2::poly::VerificationStrategy;

        let strategy = verify_proof::<Scheme, _, _, Verifier, BatchVerifier<_, _>, _>(
            &verifier_params,
            &verifier_key,
            strategy,
            &[&[&[right, top]]],
            &mut transcript,
        )
        .unwrap();

        // This is a bit ugly :/
        assert!(VerificationStrategy::<_, Verifier, _>::finalize(strategy));
        // Can't infer the strategy variant with the below
        // assert!(strategy.finalize());
    }
}
