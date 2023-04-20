use super::integer::{IntegerChip, IntegerConfig};
use crate::halo2;
use crate::integer;
use crate::maingate;
use ecc::maingate::RegionCtx;
use ecc::{AssignedPoint, EccConfig, GeneralEccChip};
use halo2::arithmetic::{CurveAffine, FieldExt};
use halo2::dev::{VerifyFailure, FailureLocation};
use halo2::{circuit::Value, plonk::Error};
use integer::rns::Integer;
use integer::{AssignedInteger, IntegerInstructions, Range};
use maingate::{AssignedCondition, MainGateConfig, RangeConfig};

use std::cell::RefCell;
use std::collections::HashMap;

#[derive(Clone, Debug)]
pub struct EcdsaConfig {
    main_gate_config: MainGateConfig,
    range_config: RangeConfig,
}

impl EcdsaConfig {
    pub fn new(range_config: RangeConfig, main_gate_config: MainGateConfig) -> Self {
        Self {
            range_config,
            main_gate_config,
        }
    }

    pub fn ecc_chip_config(&self) -> EccConfig {
        EccConfig::new(self.range_config.clone(), self.main_gate_config.clone())
    }

    pub fn integer_chip_config(&self) -> IntegerConfig {
        IntegerConfig::new(self.range_config.clone(), self.main_gate_config.clone())
    }
}

#[derive(Clone, Debug)]
pub struct EcdsaSig<
    W: FieldExt,
    N: FieldExt,
    const NUMBER_OF_LIMBS: usize,
    const BIT_LEN_LIMB: usize,
> {
    pub r: Integer<W, N, NUMBER_OF_LIMBS, BIT_LEN_LIMB>,
    pub s: Integer<W, N, NUMBER_OF_LIMBS, BIT_LEN_LIMB>,
}

pub struct AssignedEcdsaSig<
    W: FieldExt,
    N: FieldExt,
    const NUMBER_OF_LIMBS: usize,
    const BIT_LEN_LIMB: usize,
> {
    pub r: AssignedInteger<W, N, NUMBER_OF_LIMBS, BIT_LEN_LIMB>,
    pub s: AssignedInteger<W, N, NUMBER_OF_LIMBS, BIT_LEN_LIMB>,
}

pub struct AssignedPublicKey<
    W: FieldExt,
    N: FieldExt,
    const NUMBER_OF_LIMBS: usize,
    const BIT_LEN_LIMB: usize,
> {
    pub point: AssignedPoint<W, N, NUMBER_OF_LIMBS, BIT_LEN_LIMB>,
}

pub struct EcdsaChip<
    E: CurveAffine,
    N: FieldExt,
    const NUMBER_OF_LIMBS: usize,
    const BIT_LEN_LIMB: usize,
>(GeneralEccChip<E, N, NUMBER_OF_LIMBS, BIT_LEN_LIMB>);

impl<E: CurveAffine, N: FieldExt, const NUMBER_OF_LIMBS: usize, const BIT_LEN_LIMB: usize>
    EcdsaChip<E, N, NUMBER_OF_LIMBS, BIT_LEN_LIMB>
{
    pub fn new(ecc_chip: GeneralEccChip<E, N, NUMBER_OF_LIMBS, BIT_LEN_LIMB>) -> Self {
        Self(ecc_chip)
    }

    pub fn scalar_field_chip(
        &self,
    ) -> &IntegerChip<E::ScalarExt, N, NUMBER_OF_LIMBS, BIT_LEN_LIMB> {
        self.0.scalar_field_chip()
    }

    fn ecc_chip(&self) -> GeneralEccChip<E, N, NUMBER_OF_LIMBS, BIT_LEN_LIMB> {
        self.0.clone()
    }
}

impl<E: CurveAffine, N: FieldExt, const NUMBER_OF_LIMBS: usize, const BIT_LEN_LIMB: usize>
    EcdsaChip<E, N, NUMBER_OF_LIMBS, BIT_LEN_LIMB>
{
    pub fn verify(
        &self,
        ctx: &mut RegionCtx<'_, N>,
        sig: &AssignedEcdsaSig<E::Scalar, N, NUMBER_OF_LIMBS, BIT_LEN_LIMB>,
        pk: &AssignedPublicKey<E::Base, N, NUMBER_OF_LIMBS, BIT_LEN_LIMB>,
        msg_hash: &AssignedInteger<E::Scalar, N, NUMBER_OF_LIMBS, BIT_LEN_LIMB>,
        offsets: &mut HashMap<String, usize>,
        enable_skipping_invalid_signature: bool,
    ) -> Result<AssignedCondition<N>, Error> {
        let ecc_chip = self.ecc_chip();
        let scalar_chip = ecc_chip.scalar_field_chip();
        let base_chip = ecc_chip.base_field_chip();

        offsets.insert("Started at".to_string(), ctx.offset());

        // 1. check 0 < r, s < n, if r == 0 or s == 0 the signature is marked as invalid

        // since `assert_not_zero` already includes a in-field check, we can just
        // call `assert_not_zero`
        offsets.insert("1. check 0 < r, s < n".to_string(), ctx.offset());

        let is_r_valid = scalar_chip.is_not_zero(ctx, &sig.r)?;
        let is_s_valid = scalar_chip.is_not_zero(ctx, &sig.s)?;
        let is_r_s_valid = scalar_chip.and(ctx, &is_r_valid, &is_s_valid)?;

        // 2. w = s^(-1) (mod n)
        offsets.insert("2. w = s^(-1) (mod n)".to_string(), ctx.offset());
        let (s_inv, _) = scalar_chip.invert(ctx, &sig.s)?;

        // 3. u1 = m' * w (mod n)
        offsets.insert("3. u1 = m' * w (mod n)".to_string(), ctx.offset());
        let u1 = scalar_chip.mul(ctx, msg_hash, &s_inv)?;

        // 4. u2 = r * w (mod n)
        offsets.insert("4. u2 = r * w (mod n)".to_string(), ctx.offset());
        let u2 = scalar_chip.mul(ctx, &sig.r, &s_inv)?;

        // 5. compute Q = u1*G + u2*pk
        offsets.insert("5. compute Q = u1*G + u2*pk".to_string(), ctx.offset());
        let e_gen = ecc_chip.assign_point(ctx, Value::known(E::generator()))?;
        let g1 = ecc_chip.mul(ctx, &e_gen, &u1, 2)?;
        let g2 = ecc_chip.mul(ctx, &pk.point, &u2, 2)?;
        let q = ecc_chip.add(ctx, &g1, &g2)?;

        // 6. reduce q_x in E::ScalarExt
        // assuming E::Base/E::ScalarExt have the same number of limbs
        offsets.insert("6. reduce q_x in E::ScalarExt".to_string(), ctx.offset());
        let q_x = q.x();
        let q_x_reduced_in_q = base_chip.reduce(ctx, q_x)?;
        let q_x_reduced_in_r = scalar_chip.reduce_external(ctx, &q_x_reduced_in_q)?;

        // 7. check if Q.x == r (mod n)
        offsets.insert("7. check if Q.x == r (mod n)".to_string(), ctx.offset());
        let is_q_x_reduced_in_r_equal_to_r = scalar_chip.is_strict_equal(ctx, &q_x_reduced_in_r, &sig.r)?;
        
        offsets.insert("8. Check enable_skipping_invalid_signature".to_string(), ctx.offset());
        let is_valid = scalar_chip.and(ctx, &is_r_s_valid, &is_q_x_reduced_in_r_equal_to_r)?;
        let enable_skipping_invalid_signature_value = scalar_chip.assign_constant(ctx, enable_skipping_invalid_signature.into())?;
        let value_2 = 1;
        let value2 = scalar_chip.assign_constant(ctx, value_2.into())?;
        let result = scalar_chip.select(ctx, &value2, &enable_skipping_invalid_signature_value, &is_valid)?;

        scalar_chip.assert_not_zero(ctx, &result)?;

        offsets.insert("Finished at".to_string(), ctx.offset());

        Ok(is_valid)
    }
}

#[cfg(test)]
mod tests {
    use super::{AssignedEcdsaSig, AssignedPublicKey, EcdsaChip};
    use crate::halo2;
    use crate::integer;
    use crate::maingate;
    use ecc::integer::Range;
    use ecc::maingate::big_to_fe;
    use ecc::maingate::fe_to_big;
    use ecc::maingate::RegionCtx;
    use ecc::{EccConfig, GeneralEccChip};
    use group::ff::Field;
    use group::{Curve, Group};
    use halo2::arithmetic::CurveAffine;
    use halo2::arithmetic::FieldExt;
    use halo2::circuit::{Layouter, SimpleFloorPlanner, Value};
    use halo2::dev::{VerifyFailure, FailureLocation};
    use halo2::plonk::{Circuit, ConstraintSystem, Error};
    use integer::IntegerInstructions;
    use maingate::mock_prover_verify;
    use maingate::{MainGate, MainGateConfig, RangeChip, RangeConfig, RangeInstructions};
    use rand_core::OsRng;

    use std::cell::RefCell;
    use std::collections::HashMap;
    use std::fmt::{self, Debug};
    use std::marker::PhantomData;

    const BIT_LEN_LIMB: usize = 68;
    const NUMBER_OF_LIMBS: usize = 4;

    #[derive(Clone, Debug)]
    struct TestCircuitEcdsaVerifyConfig {
        main_gate_config: MainGateConfig,
        range_config: RangeConfig,
    }

    impl TestCircuitEcdsaVerifyConfig {
        pub fn new<C: CurveAffine, N: FieldExt>(meta: &mut ConstraintSystem<N>) -> Self {
            let (rns_base, rns_scalar) =
                GeneralEccChip::<C, N, NUMBER_OF_LIMBS, BIT_LEN_LIMB>::rns();
            let main_gate_config = MainGate::<N>::configure(meta);
            let mut overflow_bit_lens: Vec<usize> = vec![];
            overflow_bit_lens.extend(rns_base.overflow_lengths());
            overflow_bit_lens.extend(rns_scalar.overflow_lengths());
            let composition_bit_lens = vec![BIT_LEN_LIMB / NUMBER_OF_LIMBS];

            let range_config = RangeChip::<N>::configure(
                meta,
                &main_gate_config,
                composition_bit_lens,
                overflow_bit_lens,
            );
            TestCircuitEcdsaVerifyConfig {
                main_gate_config,
                range_config,
            }
        }

        pub fn ecc_chip_config(&self) -> EccConfig {
            EccConfig::new(self.range_config.clone(), self.main_gate_config.clone())
        }

        pub fn config_range<N: FieldExt>(
            &self,
            layouter: &mut impl Layouter<N>,
        ) -> Result<(), Error> {
            let range_chip = RangeChip::<N>::new(self.range_config.clone());
            range_chip.load_table(layouter)?;

            Ok(())
        }
    }

    #[derive(Default, Clone)]
    struct TestCircuitEcdsaVerify<E: CurveAffine, N: FieldExt> {
        public_key: Value<E>,
        signature: Value<(E::Scalar, E::Scalar)>,
        msg_hash: Value<E::Scalar>,

        aux_generator: E,
        window_size: usize,

        offsets: RefCell<HashMap<String, usize>>,

        _marker: PhantomData<N>,
    }

    impl<E: CurveAffine, N: FieldExt> Circuit<N> for TestCircuitEcdsaVerify<E, N> {
        type Config = TestCircuitEcdsaVerifyConfig;
        type FloorPlanner = SimpleFloorPlanner;

        fn without_witnesses(&self) -> Self {
            Self::default()
        }

        fn configure(meta: &mut ConstraintSystem<N>) -> Self::Config {
            TestCircuitEcdsaVerifyConfig::new::<E, N>(meta)
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<N>,
        ) -> Result<(), Error> {
            let mut ecc_chip = GeneralEccChip::<E, N, NUMBER_OF_LIMBS, BIT_LEN_LIMB>::new(
                config.ecc_chip_config(),
            );

            layouter.assign_region(
                || "assign aux values",
                |region| {
                    let offset = 0;
                    let ctx = &mut RegionCtx::new(region, offset);

                    ecc_chip.assign_aux_generator(ctx, Value::known(self.aux_generator))?;
                    ecc_chip.assign_aux(ctx, self.window_size, 1)?;
                    Ok(())
                },
            )?;

            let ecdsa_chip = EcdsaChip::new(ecc_chip.clone());
            let scalar_chip = ecc_chip.scalar_field_chip();

            layouter.assign_region(
                || "region 0",
                |region| {
                    let offset = 0;
                    let ctx = &mut RegionCtx::new(region, offset);

                    let r = self.signature.map(|signature| signature.0);
                    let s = self.signature.map(|signature| signature.1);
                    let integer_r = ecc_chip.new_unassigned_scalar(r);
                    let integer_s = ecc_chip.new_unassigned_scalar(s);
                    let msg_hash = ecc_chip.new_unassigned_scalar(self.msg_hash);

                    let r_assigned =
                        scalar_chip.assign_integer(ctx, integer_r, Range::Remainder)?;
                    let s_assigned =
                        scalar_chip.assign_integer(ctx, integer_s, Range::Remainder)?;
                    let sig = AssignedEcdsaSig {
                        r: r_assigned,
                        s: s_assigned,
                    };

                    let pk_in_circuit = ecc_chip.assign_point(ctx, self.public_key)?;
                    let pk_assigned = AssignedPublicKey {
                        point: pk_in_circuit,
                    };
                    let msg_hash = scalar_chip.assign_integer(ctx, msg_hash, Range::Remainder)?;
                    let mut my_dict: HashMap<String, usize> = HashMap::new();
                    let response = ecdsa_chip.verify(ctx, &sig, &pk_assigned, &msg_hash, &mut my_dict, false);
                    *self.offsets.borrow_mut() = my_dict;
                    return response;
                },
            )?;

            config.config_range(&mut layouter)?;

            Ok(())
        }
    }

    #[test]
    fn test_ecdsa_verifier() {
        fn mod_n<C: CurveAffine>(x: C::Base) -> C::Scalar {
            let x_big = fe_to_big(x);
            big_to_fe(x_big)
        }

        fn find_closest_key(offset: usize, hm: &RefCell<HashMap<String, usize>>) -> Option<String> {
            let mut best_key = None;
            let mut smallest_diff = std::usize::MAX;

            for (key, value) in hm.borrow().iter() {
                if offset >= *value {
                    let diff = offset - *value;
                    if diff < smallest_diff {
                        best_key = Some(key.clone());
                        smallest_diff = diff;
                    }
                }
            }

            best_key
        }

        fn run<C: CurveAffine, N: FieldExt>() {
            let g = C::generator();

            // Generate a key pair
            let sk = <C as CurveAffine>::ScalarExt::random(OsRng);
            let public_key = (g * sk).to_affine();

            // Generate a valid signature
            // Suppose `m_hash` is the message hash
            let msg_hash = <C as CurveAffine>::ScalarExt::random(OsRng);

            // Draw arandomness
            let k = <C as CurveAffine>::ScalarExt::random(OsRng);
            let k_inv = k.invert().unwrap();

            // Calculate `r`
            let r_point = (g * k).to_affine().coordinates().unwrap();
            let x = r_point.x();
            let r = mod_n::<C>(*x);

            // Calculate `s`
            let s = k_inv * (msg_hash + (r * sk));

            // Sanity check. Ensure we construct a valid signature. So lets verify it
            {
                let s_inv = s.invert().unwrap();
                let u_1 = msg_hash * s_inv;
                let u_2 = r * s_inv;
                let r_point = ((g * u_1) + (public_key * u_2))
                    .to_affine()
                    .coordinates()
                    .unwrap();
                let x_candidate = r_point.x();
                let r_candidate = mod_n::<C>(*x_candidate);
                assert_eq!(r, r_candidate);
            }

            let aux_generator = C::CurveExt::random(OsRng).to_affine();
            let circuit = TestCircuitEcdsaVerify::<C, N> {
                public_key: Value::known(public_key),

                // Set the wrong value to test invalid signature.
                signature: Value::known((-r, s)),
                msg_hash: Value::known(msg_hash),
                aux_generator,
                window_size: 2,
                ..Default::default()
            };
            let instance = vec![vec![]];
            // assert_eq!(mock_prover_verify(&circuit, instance), Ok(()));
            match mock_prover_verify(&circuit, instance) {
                Ok(_) => {
                    println!("ok");
                },
                Err(errors) => {
                    for error in errors {
                        match error {
                            VerifyFailure::ConstraintNotSatisfied {constraint, location, cell_values} => {
                                // println!("Constraint not satisfied: {:?}, location: {:?}, cell values: {:?}", constraint, location, cell_values);
                                let offsets = &circuit.offsets;
                                // println!("TestCircuitEcdsaVerify offsets {:?}", &offsets);
                                match location {
                                    FailureLocation::InRegion { region: _, offset } => {
                                        // handle constraint not satisfied error
                                        let key = find_closest_key(offset, offsets);
                                        panic!("VerifyFailure::ConstraintNotSatisfied not satisfied at offset {:?}. Constraint {:?}", offset, key);
                                    },
                                    FailureLocation::OutsideRegion { row: _ } => {
                                        // handle constraint not satisfied error at row level
                                    },
                                }
                            },
                            _ => {
                                // Handle other error types here
                            }
                        }
                    }
                }
            }
        }

        use crate::curves::bn256::Fr as BnScalar;
        use crate::curves::pasta::{Fp as PastaFp, Fq as PastaFq};
        use crate::curves::secp256k1::Secp256k1Affine as Secp256k1;
        run::<Secp256k1, BnScalar>();
        // run::<Secp256k1, PastaFp>();
        // run::<Secp256k1, PastaFq>();
    }
}
