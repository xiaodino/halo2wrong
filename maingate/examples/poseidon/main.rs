mod chip;
mod spec;

use crate::spec::Poseidon;

use chip::PoseidonInstructions;
use halo2::arithmetic::FieldExt;
use halo2::circuit::Layouter;
use halo2::circuit::SimpleFloorPlanner;
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
use maingate::halo2::poly::ipa::commitment::IPACommitmentScheme;
use maingate::AssignedValue;
use maingate::MainGate;
use maingate::MainGateConfig;
use maingate::{MainGateInstructions, RegionCtx};

use poseidon::merkle::Poseidon as Reference;

use rand_core::OsRng;

use crate::chip::PoseidonChip;

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
    fn poseidon_chip(&self, main_gate_config: MainGateConfig) -> PoseidonChip<F, RF, RP, T, RATE> {
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

fn main() {
    run_with_kzg();
    run_with_ipa();
}

fn run_with_kzg() {
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

fn run_with_ipa() {
    use halo2curves::pasta::{EqAffine, Fp};

    use halo2::poly::ipa::commitment::ParamsIPA;
    use halo2::poly::ipa::multiopen::{ProverIPA, VerifierIPA};
    use halo2::poly::ipa::strategy::BatchVerifier;

    type Scheme = IPACommitmentScheme<EqAffine>;
    type Prover<'a> = ProverIPA<'a, EqAffine>;
    type Verifier<'a> = VerifierIPA<'a, EqAffine>;

    const K: u32 = 14;
    let params = ParamsIPA::<EqAffine>::new(K);
    let verifier_params = params.verifier_params();
    let rng = OsRng;

    let left = Fp::from(0);
    let right = Fp::from(1);
    let ref_hasher = Reference::<Fp, T, RATE>::new(RF, RP);
    let top = ref_hasher.hash(&[left, right].try_into().unwrap());

    // Synthesis

    let circuit = TestCircuit {
        left: None,
        right: None,
        top: None,
        poseidon_spec: pasta_poseidon_8_55_3_2(),
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
        poseidon_spec: pasta_poseidon_8_55_3_2(),
    };

    let mut transcript = Blake2bWrite::<Vec<u8>, EqAffine, Challenge255<_>>::init(vec![]);
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

    let mut transcript = Blake2bRead::<&[u8], EqAffine, Challenge255<_>>::init(&proof);
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
