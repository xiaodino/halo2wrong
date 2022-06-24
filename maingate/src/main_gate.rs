//! `main_gate` is a five width stardart like PLONK gate that constrains the
//! equation below
//!
//! q_a * a + q_b * b + q_c * c + q_d * d + q_e * e +
//! q_mul_ab * a * b +
//! q_mul_cd * c * d +
//! q_e_next * e +
//! public_input +
//! q_constant = 0

use crate::halo2::arithmetic::FieldExt;
use crate::halo2::circuit::{Chip, Layouter};
use crate::halo2::plonk::{Advice, Column, ConstraintSystem, Error, Fixed, Instance};
use crate::halo2::poly::Rotation;
use crate::instructions::{CombinationOptionCommon, MainGateInstructions, Term};
use crate::{Assigned, AssignedCondition, AssignedValue, UnassignedValue};
use halo2wrong::RegionCtx;
use std::marker::PhantomData;

const WIDTH: usize = 5;

/// `ColumnTags` is an helper to find special columns that are frequently used
/// across gates
pub trait ColumnTags<Column> {
    /// Next row accumulator
    fn next() -> Column;
    /// First column
    fn first() -> Column;
    /// Index that last term should in linear combination
    fn last_term_index() -> usize;
}

/// Enumerates columns of the main gate
#[derive(Debug)]
pub enum MainGateColumn {
    /// A
    A = 0,
    /// B
    B = 1,
    /// C
    C = 2,
    /// D
    D = 3,
    /// E
    E = 4,
}

impl ColumnTags<MainGateColumn> for MainGateColumn {
    fn first() -> Self {
        MainGateColumn::A
    }

    fn next() -> Self {
        MainGateColumn::E
    }

    fn last_term_index() -> usize {
        Self::first() as usize
    }
}

/// Config defines fixed and witness columns of the main gate
#[derive(Clone, Debug)]
pub struct MainGateConfig {
    pub(crate) a: Column<Advice>,
    pub(crate) b: Column<Advice>,
    pub(crate) c: Column<Advice>,
    pub(crate) d: Column<Advice>,
    pub(crate) e: Column<Advice>,

    pub(crate) sa: Column<Fixed>,
    pub(crate) sb: Column<Fixed>,
    pub(crate) sc: Column<Fixed>,
    pub(crate) sd: Column<Fixed>,
    pub(crate) se: Column<Fixed>,

    pub(crate) se_next: Column<Fixed>,

    pub(crate) s_mul_ab: Column<Fixed>,
    pub(crate) s_mul_cd: Column<Fixed>,

    pub(crate) s_constant: Column<Fixed>,
    pub(crate) instance: Column<Instance>,
}

/// MainGate implements instructions with [`MainGateConfig`]
#[derive(Debug)]
pub struct MainGate<F: FieldExt> {
    config: MainGateConfig,
    _marker: PhantomData<F>,
}

impl<F: FieldExt> Chip<F> for MainGate<F> {
    type Config = MainGateConfig;
    type Loaded = ();

    fn config(&self) -> &Self::Config {
        &self.config
    }

    fn loaded(&self) -> &Self::Loaded {
        &()
    }
}

/// Additional combination customisations for this gate with two multiplication
#[derive(Clone, Debug)]
pub enum CombinationOption<F: FieldExt> {
    /// Wrapper for common combination options
    Common(CombinationOptionCommon<F>),
    /// Activates both of the multiplication gate
    OneLinerDoubleMul(F),
    /// Activates both multiplication gate and combines the result to the next
    /// row
    CombineToNextDoubleMul(F),
}

impl<F: FieldExt> From<CombinationOptionCommon<F>> for CombinationOption<F> {
    fn from(option: CombinationOptionCommon<F>) -> Self {
        CombinationOption::Common(option)
    }
}

impl<'a, F: FieldExt> MainGateInstructions<F, WIDTH> for MainGate<F> {
    type CombinationOption = CombinationOption<F>;
    type MainGateColumn = MainGateColumn;

    fn expose_public(
        &self,
        mut layouter: impl Layouter<F>,
        value: AssignedValue<F>,
        row: usize,
    ) -> Result<(), Error> {
        let config = self.config();
        layouter.constrain_instance(value.cell(), config.instance, row)
    }

    fn assign_to_column(
        &self,
        ctx: &mut RegionCtx<'_, '_, F>,
        unassigned: &UnassignedValue<F>,
        column: MainGateColumn,
    ) -> Result<AssignedValue<F>, Error> {
        let column = match column {
            MainGateColumn::A => self.config.a,
            MainGateColumn::B => self.config.b,
            MainGateColumn::C => self.config.c,
            MainGateColumn::D => self.config.d,
            MainGateColumn::E => self.config.e,
        };
        let cell = ctx.assign_advice("assign value", column, unassigned.value())?;
        // proceed to the next row
        self.no_operation(ctx)?;
        Ok(unassigned.assign(cell.cell()))
    }

    fn sub_sub_with_constant(
        &self,
        ctx: &mut RegionCtx<'_, '_, F>,
        a: &AssignedValue<F>,
        b_0: &AssignedValue<F>,
        b_1: &AssignedValue<F>,
        constant: F,
    ) -> Result<AssignedValue<F>, Error> {
        let c = match (a.value(), b_0.value(), b_1.value()) {
            (Some(a), Some(b_0), Some(b_1)) => Some(a - b_0 - b_1 + constant),
            _ => None,
        };

        Ok(self.apply(
            ctx,
            terms!([
                Term::assigned_to_add(a),
                Term::assigned_to_sub(b_0),
                Term::assigned_to_sub(b_1),
                Term::unassigned_to_sub(c),
            ]),
            constant,
            CombinationOptionCommon::OneLinerAdd.into(),
        )?[3])
    }

    fn select(
        &self,
        ctx: &mut RegionCtx<'_, '_, F>,
        a: &AssignedValue<F>,
        b: &AssignedValue<F>,
        cond: &AssignedCondition<F>,
    ) -> Result<AssignedValue<F>, Error> {
        // We should satisfy the equation below with bit asserted condition flag
        // c (a-b) + b - res = 0
        // cond * a - cond * b + b - res = 0

        // Witness layout:
        // | A   | B   | C | D   | E  |
        // | --- | --- | - | --- | ---|
        // | c   | a   | c | b   | res|

        let res = match (a.value(), b.value(), cond.bool_value) {
            (Some(a), Some(b), Some(cond)) => {
                let res = if cond { a } else { b };
                Some(res)
            }
            _ => None,
        };

        let assigned = self.apply(
            ctx,
            &[
                Term::assigned_to_mul(&cond.into()),
                Term::assigned_to_mul(a),
                Term::assigned_to_mul(&cond.into()),
                Term::assigned_to_add(b),
                Term::unassigned_to_sub(res),
            ],
            F::zero(),
            CombinationOption::OneLinerDoubleMul(-F::one()),
        )?;
        ctx.constrain_equal(assigned[0].cell(), assigned[2].cell())?;
        Ok(assigned[4])
    }

    fn select_or_assign(
        &self,
        ctx: &mut RegionCtx<'_, '_, F>,
        a: &AssignedValue<F>,
        b: F,
        cond: &AssignedCondition<F>,
    ) -> Result<AssignedValue<F>, Error> {
        // We should satisfy the equation below with bit asserted condition flag
        // c (a-b_constant) + b_constant - res = 0

        // Witness layout:
        // | A   | B   | C | D   |
        // | --- | --- | - | --- |
        // | dif | a   | - | -   |
        // | c   | dif | - | res |

        let (dif, res) = match (a.value(), cond.bool_value) {
            (Some(a), Some(cond)) => {
                let dif = a - b;
                let res = if cond { a } else { b };
                (Some(dif), Some(res))
            }
            _ => (None, None),
        };

        // a - b - dif = 0
        let dif = self.apply(
            ctx,
            terms!([Term::assigned_to_add(a), Term::unassigned_to_sub(dif)]),
            -b,
            CombinationOptionCommon::OneLinerAdd.into(),
        )?[1];

        // cond * dif + b + a_or_b  = 0
        Ok(self.apply(
            ctx,
            terms!([
                Term::assigned_to_mul(&dif),
                Term::assigned_to_mul(&cond.into()),
                Term::unassigned_to_sub(res),
            ]),
            b,
            CombinationOptionCommon::OneLinerMul.into(),
        )?[2])
    }

    fn apply(
        &self,
        ctx: &mut RegionCtx<'_, '_, F>,
        terms: &[Term<F>; WIDTH],
        constant: F,
        option: CombinationOption<F>,
    ) -> Result<[AssignedValue<F>; WIDTH], Error> {
        // Break witness and fixed value
        let (c_0, u_0) = (terms[0].coeff(), terms[0].base());
        let (c_1, u_1) = (terms[1].coeff(), terms[1].base());
        let (c_2, u_2) = (terms[2].coeff(), terms[2].base());
        let (c_3, u_3) = (terms[3].coeff(), terms[3].base());
        let (c_4, u_4) = (terms[4].coeff(), terms[4].base());

        // Assign witnesses
        let cell_0 = ctx.assign_advice("coeff_0", self.config.a, c_0)?.cell();
        let cell_1 = ctx.assign_advice("coeff_1", self.config.b, c_1)?.cell();
        let cell_2 = ctx.assign_advice("coeff_2", self.config.c, c_2)?.cell();
        let cell_3 = ctx.assign_advice("coeff_3", self.config.d, c_3)?.cell();
        let cell_4 = ctx.assign_advice("coeff_4", self.config.e, c_4)?.cell();

        // All combination options allows addition gates to be configured
        ctx.assign_fixed("base_0", self.config.sa, u_0)?;
        ctx.assign_fixed("base_1", self.config.sb, u_1)?;
        ctx.assign_fixed("base_2", self.config.sc, u_2)?;
        ctx.assign_fixed("base_3", self.config.sd, u_3)?;
        ctx.assign_fixed("base_4", self.config.se, u_4)?;

        ctx.assign_fixed("s_constant", self.config.s_constant, constant)?;

        // Given specific option configure multiplication and rotation gates
        match option {
            CombinationOption::Common(option) => match option {
                // q_a * a + q_b * b + q_c * c + q_d * d + q_e * e +
                // a * b +
                // q_e_next * e +
                // q_constant = 0
                CombinationOptionCommon::CombineToNextMul(next) => {
                    ctx.assign_fixed("s_mul_ab", self.config.s_mul_ab, F::one())?;
                    ctx.assign_fixed("s_mul_cd", self.config.s_mul_cd, F::zero())?;
                    ctx.assign_fixed("se_next", self.config.se_next, next)?;
                }

                // q_a * a + q_b * b + q_c * c + q_d * d + q_e * e +
                // q_mul_ab * a * b +
                // q_e_next * e +
                // q_constant = 0
                CombinationOptionCommon::CombineToNextScaleMul(next, n) => {
                    ctx.assign_fixed("s_mul_ab", self.config.s_mul_ab, n)?;
                    ctx.assign_fixed("s_mul_cd", self.config.s_mul_cd, F::zero())?;
                    ctx.assign_fixed("se_next", self.config.se_next, next)?;
                }

                // q_a * a + q_b * b + q_c * c + q_d * d + q_e * e +
                // q_e_next * e +
                // q_constant = 0
                CombinationOptionCommon::CombineToNextAdd(next) => {
                    ctx.assign_fixed("s_mul_ab", self.config.s_mul_ab, F::zero())?;
                    ctx.assign_fixed("s_mul_cd", self.config.s_mul_cd, F::zero())?;
                    ctx.assign_fixed("se_next", self.config.se_next, next)?;
                }

                // q_a * a + q_b * b + q_c * c + q_d * d + q_e * e +
                // q_mul_ab * a * b +
                // q_constant = 0
                CombinationOptionCommon::OneLinerMul => {
                    ctx.assign_fixed("s_mul_ab", self.config.s_mul_ab, F::one())?;
                    ctx.assign_fixed("s_mul_cd", self.config.s_mul_cd, F::zero())?;
                    ctx.assign_fixed("se_next", self.config.se_next, F::zero())?;
                }

                // q_a * a + q_b * b + q_c * c + q_d * d + q_e * e +
                // q_constant = 0
                CombinationOptionCommon::OneLinerAdd => {
                    ctx.assign_fixed("se_next", self.config.se_next, F::zero())?;
                    ctx.assign_fixed("s_mul_ab", self.config.s_mul_ab, F::zero())?;
                    ctx.assign_fixed("s_mul_cd", self.config.s_mul_cd, F::zero())?;
                }
            },

            // q_a * a + q_b * b + q_c * c + q_d * d + q_e * e +
            // q_mul_ab * a * b +
            // q_mul_cd * c * d +
            // q_e_next * e +
            // q_constant = 0
            CombinationOption::CombineToNextDoubleMul(next) => {
                ctx.assign_fixed("s_mul_ab", self.config.s_mul_ab, F::one())?;
                ctx.assign_fixed("s_mul_cd", self.config.s_mul_cd, F::one())?;
                ctx.assign_fixed("se_next", self.config.se_next, next)?;
            }

            // q_a * a + q_b * b + q_c * c + q_d * d + q_e * e +
            // q_mul_ab * a * b +
            // q_mul_cd * c * d +
            // q_constant = 0
            CombinationOption::OneLinerDoubleMul(e) => {
                ctx.assign_fixed("s_mul_ab", self.config.s_mul_ab, F::one())?;
                ctx.assign_fixed("s_mul_cd", self.config.s_mul_cd, e)?;
                ctx.assign_fixed("se_next", self.config.se_next, F::zero())?;
            }
        };

        // If given witness is already assigned apply copy constains
        match terms[0] {
            Term::Assigned(assigned, _) => ctx.region.constrain_equal(assigned.cell(), cell_0),
            _ => Ok(()),
        }?;

        match terms[1] {
            Term::Assigned(assigned, _) => ctx.region.constrain_equal(assigned.cell(), cell_1),
            _ => Ok(()),
        }?;

        match terms[2] {
            Term::Assigned(assigned, _) => ctx.region.constrain_equal(assigned.cell(), cell_2),
            _ => Ok(()),
        }?;

        match terms[3] {
            Term::Assigned(assigned, _) => ctx.region.constrain_equal(assigned.cell(), cell_3),
            _ => Ok(()),
        }?;

        match terms[4] {
            Term::Assigned(assigned, _) => ctx.region.constrain_equal(assigned.cell(), cell_4),
            _ => Ok(()),
        }?;

        // Proceed to next row
        ctx.next();

        // Return new assigned values at this level os that they can be used for further
        // constaints
        let a_0 = AssignedValue::new(cell_0, c_0);
        let a_1 = AssignedValue::new(cell_1, c_1);
        let a_2 = AssignedValue::new(cell_2, c_2);
        let a_3 = AssignedValue::new(cell_3, c_3);
        let a_4 = AssignedValue::new(cell_4, c_4);

        Ok([a_0, a_1, a_2, a_3, a_4])
    }

    /// Skip this row without any operation
    fn no_operation(&self, ctx: &mut RegionCtx<'_, '_, F>) -> Result<(), Error> {
        ctx.assign_fixed("s_mul_ab", self.config.s_mul_ab, F::zero())?;
        ctx.assign_fixed("s_mul_cd", self.config.s_mul_cd, F::zero())?;
        ctx.assign_fixed("sc", self.config.sc, F::zero())?;
        ctx.assign_fixed("sa", self.config.sa, F::zero())?;
        ctx.assign_fixed("sb", self.config.sb, F::zero())?;
        ctx.assign_fixed("sd", self.config.sd, F::zero())?;
        ctx.assign_fixed("se", self.config.se, F::zero())?;
        ctx.assign_fixed("se_next", self.config.se_next, F::zero())?;
        ctx.assign_fixed("s_constant", self.config.s_constant, F::zero())?;
        ctx.next();
        Ok(())
    }
}

impl<F: FieldExt> MainGate<F> {
    /// Create new main gate with given config
    pub fn new(config: MainGateConfig) -> Self {
        MainGate {
            config,
            _marker: PhantomData,
        }
    }

    /// Configures polynomial relationships and returns the resuiting config
    pub fn configure(meta: &mut ConstraintSystem<F>) -> MainGateConfig {
        let a = meta.advice_column();
        let b = meta.advice_column();
        let c = meta.advice_column();
        let d = meta.advice_column();
        let e = meta.advice_column();

        let sa = meta.fixed_column();
        let sb = meta.fixed_column();
        let sc = meta.fixed_column();
        let sd = meta.fixed_column();
        let se = meta.fixed_column();

        let s_mul_ab = meta.fixed_column();
        let s_mul_cd = meta.fixed_column();

        let se_next = meta.fixed_column();
        let s_constant = meta.fixed_column();

        let instance = meta.instance_column();

        meta.enable_equality(a);
        meta.enable_equality(b);
        meta.enable_equality(c);
        meta.enable_equality(d);
        meta.enable_equality(e);
        meta.enable_equality(instance);

        meta.create_gate("main_gate", |meta| {
            let a = meta.query_advice(a, Rotation::cur());
            let b = meta.query_advice(b, Rotation::cur());
            let c = meta.query_advice(c, Rotation::cur());
            let d = meta.query_advice(d, Rotation::cur());
            let e_next = meta.query_advice(e, Rotation::next());
            let e = meta.query_advice(e, Rotation::cur());

            let sa = meta.query_fixed(sa, Rotation::cur());
            let sb = meta.query_fixed(sb, Rotation::cur());
            let sc = meta.query_fixed(sc, Rotation::cur());
            let sd = meta.query_fixed(sd, Rotation::cur());
            let se = meta.query_fixed(se, Rotation::cur());

            let se_next = meta.query_fixed(se_next, Rotation::cur());

            let s_mul_ab = meta.query_fixed(s_mul_ab, Rotation::cur());
            let s_mul_cd = meta.query_fixed(s_mul_cd, Rotation::cur());

            let s_constant = meta.query_fixed(s_constant, Rotation::cur());

            vec![
                a.clone() * sa
                    + b.clone() * sb
                    + c.clone() * sc
                    + d.clone() * sd
                    + e * se
                    + a * b * s_mul_ab
                    + c * d * s_mul_cd
                    + se_next * e_next
                    + s_constant,
            ]
        });

        MainGateConfig {
            a,
            b,
            c,
            d,
            e,
            sa,
            sb,
            sc,
            sd,
            se,
            se_next,
            s_constant,
            s_mul_ab,
            s_mul_cd,
            instance,
        }
    }
}

#[cfg(test)]
mod tests {

    use super::{MainGate, MainGateConfig, Term};
    use crate::curves::pasta::Fp;
    use crate::halo2::arithmetic::FieldExt;
    use crate::halo2::circuit::{Layouter, SimpleFloorPlanner};
    use crate::halo2::dev::MockProver;
    use crate::halo2::plonk::{Circuit, ConstraintSystem, Error};
    use crate::main_gate::{CombinationOptionCommon, MainGateInstructions};
    use crate::{AssignedCondition, UnassignedValue};
    use group::ff::PrimeField;
    use halo2wrong::utils::{big_to_fe, decompose};
    use halo2wrong::RegionCtx;
    use rand_core::OsRng;
    use std::marker::PhantomData;

    #[derive(Clone)]
    struct TestCircuitConfig {
        main_gate_config: MainGateConfig,
    }

    impl TestCircuitConfig {
        fn main_gate<F: FieldExt>(&self) -> MainGate<F> {
            MainGate::<F> {
                config: self.main_gate_config.clone(),
                _marker: PhantomData,
            }
        }
    }

    #[derive(Default)]
    struct TestCircuitPublicInputs<F: FieldExt> {
        _marker: PhantomData<F>,
        public_input: F,
    }

    impl<F: FieldExt> Circuit<F> for TestCircuitPublicInputs<F> {
        type Config = TestCircuitConfig;
        type FloorPlanner = SimpleFloorPlanner;

        fn without_witnesses(&self) -> Self {
            Self::default()
        }

        fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
            let main_gate_config = MainGate::<F>::configure(meta);
            TestCircuitConfig { main_gate_config }
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<F>,
        ) -> Result<(), Error> {
            let main_gate = config.main_gate();

            let value = layouter.assign_region(
                || "region 0",
                |mut region| {
                    let offset = &mut 0;
                    let ctx = &mut RegionCtx::new(&mut region, offset);
                    let value = main_gate.assign_value(ctx, &Some(self.public_input).into())?;
                    Ok(value)
                },
            )?;
            main_gate.expose_public(layouter, value, 0)?;
            Ok(())
        }
    }

    #[test]
    fn test_main_gate_public_inputs() {
        const K: u32 = 8;

        let public_input = Fp::from(3);
        let public_inputs = vec![vec![public_input]];

        let circuit = TestCircuitPublicInputs::<Fp> {
            public_input,
            _marker: PhantomData,
        };
        let prover = match MockProver::run(K, &circuit, public_inputs) {
            Ok(prover) => prover,
            Err(e) => panic!("{:#?}", e),
        };
        assert_eq!(prover.verify(), Ok(()));
    }

    #[derive(Default)]
    struct TestCircuitCombination<F: FieldExt> {
        _marker: PhantomData<F>,
    }

    impl<F: FieldExt> Circuit<F> for TestCircuitCombination<F> {
        type Config = TestCircuitConfig;
        type FloorPlanner = SimpleFloorPlanner;

        fn without_witnesses(&self) -> Self {
            Self::default()
        }

        fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
            let main_gate_config = MainGate::<F>::configure(meta);
            TestCircuitConfig { main_gate_config }
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<F>,
        ) -> Result<(), Error> {
            let main_gate = config.main_gate();

            let rand = || -> F { F::random(OsRng) };

            layouter.assign_region(
                || "region 0",
                |mut region| {
                    let offset = &mut 0;
                    let ctx = &mut RegionCtx::new(&mut region, offset);

                    // OneLinerAdd
                    {
                        let (a_0, a_1, a_2, a_3, a_4) = (rand(), rand(), rand(), rand(), rand());
                        let (r_0, r_1, r_2, r_3, r_4) = (rand(), rand(), rand(), rand(), rand());

                        let constant = -(a_0 * r_0 + a_1 * r_1 + a_2 * r_2 + a_3 * r_3 + a_4 * r_4);

                        let terms = [
                            Term::Unassigned(Some(a_0), r_0),
                            Term::Unassigned(Some(a_1), r_1),
                            Term::Unassigned(Some(a_2), r_2),
                            Term::Unassigned(Some(a_3), r_3),
                            Term::Unassigned(Some(a_4), r_4),
                        ];

                        let assigned = main_gate.apply(
                            ctx,
                            &terms,
                            constant,
                            CombinationOptionCommon::OneLinerAdd.into(),
                        )?;

                        let terms: Vec<Term<F>> = assigned
                            .iter()
                            .zip(vec![r_0, r_1, r_2, r_3, r_4].iter())
                            .map(|(u, r)| Term::Assigned(*u, *r))
                            .collect();

                        main_gate.apply(
                            ctx,
                            &terms.try_into().unwrap(),
                            constant,
                            CombinationOptionCommon::OneLinerAdd.into(),
                        )?;
                    }

                    // OneLinerMul
                    {
                        let (a_0, a_1, a_2, a_3, a_4) = (rand(), rand(), rand(), rand(), rand());
                        let (r_0, r_1, r_2, r_3, r_4) = (rand(), rand(), rand(), rand(), rand());

                        let constant = -(a_0 * a_1
                            + a_0 * r_0
                            + a_1 * r_1
                            + a_2 * r_2
                            + a_3 * r_3
                            + a_4 * r_4);

                        let terms = [
                            Term::Unassigned(Some(a_0), r_0),
                            Term::Unassigned(Some(a_1), r_1),
                            Term::Unassigned(Some(a_2), r_2),
                            Term::Unassigned(Some(a_3), r_3),
                            Term::Unassigned(Some(a_4), r_4),
                        ];

                        let assigned = main_gate.apply(
                            ctx,
                            &terms,
                            constant,
                            CombinationOptionCommon::OneLinerMul.into(),
                        )?;

                        let terms: Vec<Term<F>> = assigned
                            .iter()
                            .zip(vec![r_0, r_1, r_2, r_3, r_4].iter())
                            .map(|(u, r)| Term::Assigned(*u, *r))
                            .collect();

                        main_gate.apply(
                            ctx,
                            &terms.try_into().unwrap(),
                            constant,
                            CombinationOptionCommon::OneLinerMul.into(),
                        )?;
                    }

                    // CombineToNextMul(F)
                    {
                        let (a_0, a_1, a_2, a_3, a_4, a_next) =
                            (rand(), rand(), rand(), rand(), rand(), rand());
                        let (r_0, r_1, r_2, r_3, r_4, r_next) =
                            (rand(), rand(), rand(), rand(), rand(), rand());

                        let constant = -(a_0 * a_1
                            + r_0 * a_0
                            + r_1 * a_1
                            + a_2 * r_2
                            + a_3 * r_3
                            + a_4 * r_4
                            + a_next * r_next);

                        let terms = [
                            Term::Unassigned(Some(a_0), r_0),
                            Term::Unassigned(Some(a_1), r_1),
                            Term::Unassigned(Some(a_2), r_2),
                            Term::Unassigned(Some(a_3), r_3),
                            Term::Unassigned(Some(a_4), r_4),
                        ];

                        let assigned = main_gate.apply(
                            ctx,
                            &terms,
                            constant,
                            CombinationOptionCommon::CombineToNextMul(r_next).into(),
                        )?;

                        main_gate.assign_to_acc(ctx, &Some(a_next).into())?;

                        let terms: Vec<Term<F>> = assigned
                            .iter()
                            .zip(vec![r_0, r_1, r_2, r_3, r_4].iter())
                            .map(|(u, r)| Term::Assigned(*u, *r))
                            .collect();

                        main_gate.apply(
                            ctx,
                            &terms.try_into().unwrap(),
                            constant,
                            CombinationOptionCommon::CombineToNextMul(r_next).into(),
                        )?;

                        main_gate.assign_to_acc(ctx, &Some(a_next).into())?;
                    }

                    // CombineToNextScaleMul(F, F)
                    {
                        let (a_0, a_1, a_2, a_3, a_4, a_next) =
                            (rand(), rand(), rand(), rand(), rand(), rand());
                        let (r_scale, r_0, r_1, r_2, r_3, r_4, r_next) =
                            (rand(), rand(), rand(), rand(), rand(), rand(), rand());

                        let constant = -(r_scale * a_0 * a_1
                            + r_0 * a_0
                            + r_1 * a_1
                            + a_2 * r_2
                            + a_3 * r_3
                            + a_4 * r_4
                            + a_next * r_next);

                        let terms = [
                            Term::Unassigned(Some(a_0), r_0),
                            Term::Unassigned(Some(a_1), r_1),
                            Term::Unassigned(Some(a_2), r_2),
                            Term::Unassigned(Some(a_3), r_3),
                            Term::Unassigned(Some(a_4), r_4),
                        ];

                        let assigned = main_gate.apply(
                            ctx,
                            &terms,
                            constant,
                            CombinationOptionCommon::CombineToNextScaleMul(r_next, r_scale).into(),
                        )?;

                        main_gate.assign_to_acc(ctx, &Some(a_next).into())?;

                        let terms: Vec<Term<F>> = assigned
                            .iter()
                            .zip(vec![r_0, r_1, r_2, r_3, r_4].iter())
                            .map(|(u, r)| Term::Assigned(*u, *r))
                            .collect();

                        main_gate.apply(
                            ctx,
                            &terms.try_into().unwrap(),
                            constant,
                            CombinationOptionCommon::CombineToNextScaleMul(r_next, r_scale).into(),
                        )?;

                        main_gate.assign_to_acc(ctx, &Some(a_next).into())?;
                    }

                    // CombineToNextAdd(F)
                    {
                        let (a_0, a_1, a_2, a_3, a_4, a_next) =
                            (rand(), rand(), rand(), rand(), rand(), rand());
                        let (r_0, r_1, r_2, r_3, r_4, r_next) =
                            (rand(), rand(), rand(), rand(), rand(), rand());

                        let constant = -(r_0 * a_0
                            + r_1 * a_1
                            + a_2 * r_2
                            + a_3 * r_3
                            + a_4 * r_4
                            + a_next * r_next);

                        let terms = [
                            Term::Unassigned(Some(a_0), r_0),
                            Term::Unassigned(Some(a_1), r_1),
                            Term::Unassigned(Some(a_2), r_2),
                            Term::Unassigned(Some(a_3), r_3),
                            Term::Unassigned(Some(a_4), r_4),
                        ];

                        let assigned = main_gate.apply(
                            ctx,
                            &terms,
                            constant,
                            CombinationOptionCommon::CombineToNextAdd(r_next).into(),
                        )?;

                        main_gate.assign_to_acc(ctx, &Some(a_next).into())?;

                        let terms: Vec<Term<F>> = assigned
                            .iter()
                            .zip(vec![r_0, r_1, r_2, r_3, r_4].iter())
                            .map(|(u, r)| Term::Assigned(*u, *r))
                            .collect();

                        main_gate.apply(
                            ctx,
                            &terms.try_into().unwrap(),
                            constant,
                            CombinationOptionCommon::CombineToNextAdd(r_next).into(),
                        )?;

                        main_gate.assign_to_acc(ctx, &Some(a_next).into())?;
                    }

                    Ok(())
                },
            )?;

            Ok(())
        }
    }

    #[test]
    fn test_main_gate_combination() {
        const K: u32 = 8;
        let circuit = TestCircuitCombination::<Fp> {
            _marker: PhantomData,
        };
        let public_inputs = vec![vec![]];
        let prover = match MockProver::run(K, &circuit, public_inputs) {
            Ok(prover) => prover,
            Err(e) => panic!("{:#?}", e),
        };
        assert_eq!(prover.verify(), Ok(()));
    }

    #[derive(Default)]
    struct TestCircuitBitness<F: FieldExt> {
        neg_path: bool,
        _marker: PhantomData<F>,
    }

    impl<F: FieldExt> Circuit<F> for TestCircuitBitness<F> {
        type Config = TestCircuitConfig;
        type FloorPlanner = SimpleFloorPlanner;

        fn without_witnesses(&self) -> Self {
            Self::default()
        }

        fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
            let main_gate_config = MainGate::<F>::configure(meta);
            TestCircuitConfig { main_gate_config }
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<F>,
        ) -> Result<(), Error> {
            let main_gate = config.main_gate();

            layouter.assign_region(
                || "region 0",
                |mut region| {
                    let offset = &mut 0;
                    let ctx = &mut RegionCtx::new(&mut region, offset);

                    if self.neg_path {
                        let minus_one = -F::one();
                        main_gate.assign_bit(ctx, &UnassignedValue(Some(minus_one)))?;
                    } else {
                        let one = F::one();
                        let zero = F::zero();

                        let u = main_gate.assign_bit(ctx, &UnassignedValue(Some(one)))?;
                        main_gate.assert_bit(ctx, &u)?;

                        let u = main_gate.assign_bit(ctx, &UnassignedValue(Some(zero)))?;
                        main_gate.assert_bit(ctx, &u)?;
                    }

                    Ok(())
                },
            )?;

            Ok(())
        }
    }

    #[test]
    fn test_main_gate_bitness() {
        const K: u32 = 8;
        let circuit = TestCircuitBitness::<Fp> {
            neg_path: false,
            _marker: PhantomData,
        };
        let public_inputs = vec![vec![]];
        let prover = match MockProver::run(K, &circuit, public_inputs) {
            Ok(prover) => prover,
            Err(e) => panic!("{:#?}", e),
        };
        assert_eq!(prover.verify(), Ok(()));

        let circuit = TestCircuitBitness::<Fp> {
            neg_path: true,
            _marker: PhantomData,
        };
        let public_inputs = vec![vec![]];
        let prover = match MockProver::run(K, &circuit, public_inputs) {
            Ok(prover) => prover,
            Err(e) => panic!("{:#?}", e),
        };
        assert_ne!(prover.verify(), Ok(()));
    }

    #[derive(Default)]
    struct TestCircuitEquality<F: FieldExt> {
        neg_path: bool,
        _marker: PhantomData<F>,
    }

    impl<F: FieldExt> Circuit<F> for TestCircuitEquality<F> {
        type Config = TestCircuitConfig;
        type FloorPlanner = SimpleFloorPlanner;

        fn without_witnesses(&self) -> Self {
            Self::default()
        }

        fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
            let main_gate_config = MainGate::<F>::configure(meta);
            TestCircuitConfig { main_gate_config }
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<F>,
        ) -> Result<(), Error> {
            let main_gate = config.main_gate();

            layouter.assign_region(
                || "region 0",
                |mut region| {
                    let offset = &mut 0;
                    let ctx = &mut RegionCtx::new(&mut region, offset);

                    let rand = || -> F { F::random(OsRng) };

                    if self.neg_path {
                    } else {
                        let one = F::one();
                        let zero = F::zero();

                        let assigned_one = &main_gate.assign_bit(ctx, &Some(one).into())?;
                        let assigned_zero = &main_gate.assign_bit(ctx, &Some(zero).into())?;

                        // assert_equal_to_constant

                        let val = rand();
                        let assigned = &main_gate.assign_value(ctx, &Some(val).into())?;
                        main_gate.assert_equal_to_constant(ctx, assigned, val)?;
                        main_gate.assert_not_zero(ctx, assigned)?;

                        // assert_equal

                        let val = rand();
                        let assigned_0 = main_gate.assign_value(ctx, &Some(val).into())?;
                        let assigned_1 = main_gate.assign_value(ctx, &Some(val).into())?;
                        main_gate.assert_equal(ctx, &assigned_0, &assigned_1)?;

                        // assert_not_equal

                        let val_0 = rand();
                        let val_1 = rand();
                        let assigned_0 = main_gate.assign_value(ctx, &Some(val_0).into())?;
                        let assigned_1 = main_gate.assign_value(ctx, &Some(val_1).into())?;
                        main_gate.assert_not_equal(ctx, &assigned_0, &assigned_1)?;

                        // is_equal

                        let val = rand();
                        let assigned_0 = main_gate.assign_value(ctx, &Some(val).into())?;
                        let assigned_1 = main_gate.assign_value(ctx, &Some(val).into())?;
                        let is_equal = main_gate.is_equal(ctx, &assigned_0, &assigned_1)?;

                        main_gate.assert_one(ctx, &is_equal.into())?;
                        main_gate.assert_equal(ctx, &is_equal.into(), &assigned_one.into())?;

                        let val_0 = rand();
                        let val_1 = rand();
                        let assigned_0 = main_gate.assign_value(ctx, &Some(val_0).into())?;
                        let assigned_1 = main_gate.assign_value(ctx, &Some(val_1).into())?;
                        let is_equal = &main_gate.is_equal(ctx, &assigned_0, &assigned_1)?;

                        main_gate.assert_zero(ctx, &is_equal.into())?;
                        main_gate.assert_equal(ctx, &is_equal.into(), &assigned_zero.into())?;

                        // is_zero

                        let val = rand();
                        let assigned = main_gate.assign_value(ctx, &Some(val).into())?;
                        let is_zero = &main_gate.is_zero(ctx, &assigned)?;
                        main_gate.assert_zero(ctx, &is_zero.into())?;
                        main_gate.assert_equal(ctx, &is_zero.into(), &assigned_zero.into())?;

                        let is_zero = &main_gate.is_zero(ctx, &assigned_zero.into())?;
                        main_gate.assert_one(ctx, &is_zero.into())?;
                        main_gate.assert_equal(ctx, &is_zero.into(), &assigned_one.into())?;
                    }

                    Ok(())
                },
            )?;

            Ok(())
        }
    }

    #[test]
    fn test_main_gate_equaility() {
        const K: u32 = 8;
        let circuit = TestCircuitEquality::<Fp> {
            neg_path: false,
            _marker: PhantomData,
        };
        let public_inputs = vec![vec![]];
        let prover = match MockProver::run(K, &circuit, public_inputs) {
            Ok(prover) => prover,
            Err(e) => panic!("{:#?}", e),
        };
        assert_eq!(prover.verify(), Ok(()));
    }

    #[derive(Default)]
    struct TestCircuitArith<F: FieldExt> {
        _marker: PhantomData<F>,
    }

    impl<F: FieldExt> Circuit<F> for TestCircuitArith<F> {
        type Config = TestCircuitConfig;
        type FloorPlanner = SimpleFloorPlanner;

        fn without_witnesses(&self) -> Self {
            Self::default()
        }

        fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
            let main_gate_config = MainGate::<F>::configure(meta);
            TestCircuitConfig { main_gate_config }
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<F>,
        ) -> Result<(), Error> {
            let main_gate = config.main_gate();

            let rand = || -> F { F::random(OsRng) };

            layouter.assign_region(
                || "region 0",
                |mut region| {
                    let offset = &mut 0;
                    let ctx = &mut RegionCtx::new(&mut region, offset);

                    let a = rand();
                    let b = rand();
                    let c = a + b;
                    let a = Some(a);
                    let b = Some(b);
                    let c = Some(c);

                    let a = main_gate.assign_value(ctx, &a.into())?;
                    let b = main_gate.assign_value(ctx, &b.into())?;
                    let c_0 = main_gate.assign_value(ctx, &c.into())?;
                    let c_1 = main_gate.add(ctx, &a, &b)?;
                    main_gate.assert_equal(ctx, &c_0, &c_1)?;

                    let a = rand();
                    let b = rand();
                    let c = a + b;
                    let a = Some(a);
                    let c = Some(c);

                    let a = main_gate.assign_value(ctx, &a.into())?;
                    let c_0 = main_gate.assign_value(ctx, &c.into())?;
                    let c_1 = main_gate.add_constant(ctx, &a, b)?;
                    main_gate.assert_equal(ctx, &c_0, &c_1)?;

                    let a = rand();
                    let b = rand();
                    let constant = rand();
                    let c = a + b + constant;
                    let a = Some(a);
                    let b = Some(b);
                    let c = Some(c);

                    let a = main_gate.assign_value(ctx, &a.into())?;
                    let b = main_gate.assign_value(ctx, &b.into())?;
                    let c_0 = main_gate.assign_value(ctx, &c.into())?;
                    let c_1 = main_gate.add_with_constant(ctx, &a, &b, constant)?;
                    main_gate.assert_equal(ctx, &c_0, &c_1)?;

                    let a = rand();
                    let b = rand();
                    let c = a - b;
                    let a = Some(a);
                    let b = Some(b);
                    let c = Some(c);

                    let a = main_gate.assign_value(ctx, &a.into())?;
                    let b = main_gate.assign_value(ctx, &b.into())?;
                    let c_0 = main_gate.assign_value(ctx, &c.into())?;
                    let c_1 = main_gate.sub(ctx, &a, &b)?;
                    main_gate.assert_equal(ctx, &c_0, &c_1)?;

                    let a = rand();
                    let b = rand();
                    let constant = rand();
                    let c = a - b + constant;
                    let a = Some(a);
                    let b = Some(b);
                    let c = Some(c);

                    let a = main_gate.assign_value(ctx, &a.into())?;
                    let b = main_gate.assign_value(ctx, &b.into())?;
                    let c_0 = main_gate.assign_value(ctx, &c.into())?;
                    let c_1 = main_gate.sub_with_constant(ctx, &a, &b, constant)?;
                    main_gate.assert_equal(ctx, &c_0, &c_1)?;

                    let a = rand();
                    let b = rand();
                    let c = a * b;
                    let a = Some(a);
                    let b = Some(b);
                    let c = Some(c);

                    let a = main_gate.assign_value(ctx, &a.into())?;
                    let b = main_gate.assign_value(ctx, &b.into())?;
                    let c_0 = main_gate.assign_value(ctx, &c.into())?;
                    let c_1 = main_gate.mul(ctx, &a, &b)?;
                    main_gate.assert_equal(ctx, &c_0, &c_1)?;

                    let a = rand();
                    let b = rand();
                    let c = a * b.invert().unwrap();
                    let a = Some(a);
                    let b = Some(b);
                    let c = Some(c);

                    let a = main_gate.assign_value(ctx, &a.into())?;
                    let b = main_gate.assign_value(ctx, &b.into())?;
                    let c_0 = main_gate.assign_value(ctx, &c.into())?;
                    let (c_1, _) = main_gate.div(ctx, &a, &b)?;
                    main_gate.assert_equal(ctx, &c_0, &c_1)?;

                    Ok(())
                },
            )?;

            Ok(())
        }
    }

    #[test]
    fn test_main_gate_arith() {
        const K: u32 = 8;

        let circuit = TestCircuitArith::<Fp> {
            _marker: PhantomData::<Fp>,
        };
        let public_inputs = vec![vec![]];
        let prover = match MockProver::run(K, &circuit, public_inputs) {
            Ok(prover) => prover,
            Err(e) => panic!("{:#?}", e),
        };

        assert_eq!(prover.verify(), Ok(()));
    }

    #[derive(Default)]
    struct TestCircuitConditionals<F: FieldExt> {
        _marker: PhantomData<F>,
    }

    impl<F: FieldExt> Circuit<F> for TestCircuitConditionals<F> {
        type Config = TestCircuitConfig;
        type FloorPlanner = SimpleFloorPlanner;

        fn without_witnesses(&self) -> Self {
            Self::default()
        }

        fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
            let main_gate_config = MainGate::<F>::configure(meta);
            TestCircuitConfig { main_gate_config }
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<F>,
        ) -> Result<(), Error> {
            let main_gate = MainGate::<F> {
                config: config.main_gate_config,
                _marker: PhantomData,
            };

            let rand = || -> F { F::random(OsRng) };

            layouter.assign_region(
                || "region 0",
                |mut region| {
                    let offset = &mut 0;
                    let ctx = &mut RegionCtx::new(&mut region, offset);

                    let a = rand();
                    let b = rand();
                    let cond = F::zero();

                    let a = Some(a);
                    let b = Some(b);
                    let cond = Some(cond);

                    let a = &main_gate.assign_value(ctx, &a.into())?;
                    let b = &main_gate.assign_value(ctx, &b.into())?;
                    let cond: AssignedCondition<F> =
                        main_gate.assign_value(ctx, &cond.into())?.into();
                    let selected = main_gate.select(ctx, a, b, &cond)?;
                    main_gate.assert_equal(ctx, b, &selected)?;

                    let a = rand();
                    let b = rand();
                    let cond = F::one();

                    let a = Some(a);
                    let b = Some(b);
                    let cond = Some(cond);

                    let a = &main_gate.assign_value(ctx, &a.into())?;
                    let b = &main_gate.assign_value(ctx, &b.into())?;
                    let cond: AssignedCondition<F> =
                        main_gate.assign_value(ctx, &cond.into())?.into();
                    let selected = main_gate.select(ctx, a, b, &cond)?;
                    main_gate.assert_equal(ctx, a, &selected)?;

                    let a = rand();
                    let b_constant = rand();
                    let cond = F::zero();

                    let a = Some(a);
                    let b_unassigned = Some(b_constant);
                    let cond = Some(cond);

                    let a = &main_gate.assign_value(ctx, &a.into())?;
                    let b_assigned = &main_gate.assign_value(ctx, &b_unassigned.into())?;
                    let cond: AssignedCondition<F> =
                        main_gate.assign_value(ctx, &cond.into())?.into();
                    let selected = main_gate.select_or_assign(ctx, a, b_constant, &cond)?;
                    main_gate.assert_equal(ctx, b_assigned, &selected)?;

                    let a = rand();
                    let b_constant = rand();
                    let cond = F::one();

                    let a = Some(a);
                    let cond = Some(cond);

                    let a = &main_gate.assign_value(ctx, &a.into())?;
                    let cond: AssignedCondition<F> =
                        main_gate.assign_value(ctx, &cond.into())?.into();
                    let selected = main_gate.select_or_assign(ctx, a, b_constant, &cond)?;
                    main_gate.assert_equal(ctx, a, &selected)?;

                    Ok(())
                },
            )?;

            Ok(())
        }
    }

    #[test]
    fn test_main_gate_cond() {
        const K: u32 = 8;

        let circuit = TestCircuitConditionals::<Fp> {
            _marker: PhantomData::<Fp>,
        };
        let public_inputs = vec![vec![]];
        let prover = match MockProver::run(K, &circuit, public_inputs) {
            Ok(prover) => prover,
            Err(e) => panic!("{:#?}", e),
        };

        assert_eq!(prover.verify(), Ok(()));
    }

    #[derive(Default)]
    struct TestCircuitDecomposition<F: FieldExt> {
        _marker: PhantomData<F>,
        number_of_bits: usize,
    }

    impl<F: FieldExt> Circuit<F> for TestCircuitDecomposition<F> {
        type Config = TestCircuitConfig;
        type FloorPlanner = SimpleFloorPlanner;

        fn without_witnesses(&self) -> Self {
            Self::default()
        }

        fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
            let main_gate_config = MainGate::<F>::configure(meta);
            TestCircuitConfig { main_gate_config }
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<F>,
        ) -> Result<(), Error> {
            let main_gate = MainGate::<F> {
                config: config.main_gate_config,
                _marker: PhantomData,
            };

            let rand = || -> F { F::random(OsRng) };

            layouter.assign_region(
                || "region 0",
                |mut region| {
                    let offset = &mut 0;
                    let ctx = &mut RegionCtx::new(&mut region, offset);

                    let a = rand();
                    let number_of_bits = F::NUM_BITS as usize;
                    let decomposed = decompose(a, number_of_bits, 1);
                    let a = main_gate.assign_value(ctx, &Some(a).into())?;
                    let a_decomposed = main_gate.to_bits(ctx, &a, number_of_bits)?;
                    assert_eq!(decomposed.len(), a_decomposed.len());

                    for (assigned, value) in a_decomposed.iter().zip(decomposed.into_iter()) {
                        if value == F::zero() {
                            main_gate.assert_zero(ctx, &assigned.into())?;
                        } else {
                            main_gate.assert_one(ctx, &assigned.into())?;
                        }
                    }

                    let number_of_bits = self.number_of_bits;
                    use num_bigint::BigUint as big_uint;
                    use num_bigint::RandomBits;
                    use rand::Rng;
                    let a: big_uint = OsRng.sample(RandomBits::new(number_of_bits as u64));
                    let a: F = big_to_fe(a);
                    let decomposed = decompose(a, number_of_bits, 1);
                    let a = main_gate.assign_value(ctx, &Some(a).into())?;
                    let a_decomposed = main_gate.to_bits(ctx, &a, number_of_bits)?;
                    assert_eq!(decomposed.len(), a_decomposed.len());

                    Ok(())
                },
            )?;

            Ok(())
        }
    }

    #[test]
    fn test_main_gate_decomposition() {
        const K: u32 = 10;

        const NUM_BITS: u32 = Fp::NUM_BITS;

        for number_of_bits in 1..NUM_BITS as usize {
            let circuit = TestCircuitDecomposition::<Fp> {
                _marker: PhantomData::<Fp>,
                number_of_bits,
            };

            let public_inputs = vec![vec![]];
            let prover = match MockProver::run(K, &circuit, public_inputs) {
                Ok(prover) => prover,
                Err(e) => panic!("{:#?}", e),
            };

            assert_eq!(prover.verify(), Ok(()));
        }
    }

    #[derive(Default)]
    struct TestCircuitComposition<F: FieldExt> {
        _marker: PhantomData<F>,
    }

    impl<F: FieldExt> Circuit<F> for TestCircuitComposition<F> {
        type Config = TestCircuitConfig;
        type FloorPlanner = SimpleFloorPlanner;

        fn without_witnesses(&self) -> Self {
            Self::default()
        }

        fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
            let main_gate_config = MainGate::<F>::configure(meta);
            TestCircuitConfig { main_gate_config }
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<F>,
        ) -> Result<(), Error> {
            let main_gate = MainGate::<F> {
                config: config.main_gate_config,
                _marker: PhantomData,
            };

            let rand = || -> F { F::random(OsRng) };

            layouter.assign_region(
                || "region 0",
                |mut region| {
                    let offset = &mut 0;
                    let ctx = &mut RegionCtx::new(&mut region, offset);

                    for number_of_terms in 1..50 {
                        let constant = rand();
                        let terms = (0..number_of_terms)
                            .map(|_| (Term::Unassigned(Some(rand()), rand())))
                            .collect::<Vec<Term<F>>>();
                        let expected = Term::compose(&terms, constant);
                        let expected = main_gate.assign_value(ctx, &expected.into())?;
                        let result = main_gate.compose(ctx, &terms, constant)?;
                        main_gate.assert_equal(ctx, &expected, &result)?;
                    }

                    Ok(())
                },
            )?;

            Ok(())
        }
    }

    #[test]
    fn test_main_gate_composition() {
        const K: u32 = 10;
        let circuit = TestCircuitComposition::<Fp> {
            _marker: PhantomData::<Fp>,
        };
        let public_inputs = vec![vec![]];
        let prover = match MockProver::run(K, &circuit, public_inputs) {
            Ok(prover) => prover,
            Err(e) => panic!("{:#?}", e),
        };
        assert_eq!(prover.verify(), Ok(()));
    }

    #[derive(Default)]
    struct TestCircuitSign<F: FieldExt> {
        _marker: PhantomData<F>,
    }

    impl<F: FieldExt> Circuit<F> for TestCircuitSign<F> {
        type Config = TestCircuitConfig;
        type FloorPlanner = SimpleFloorPlanner;

        fn without_witnesses(&self) -> Self {
            Self::default()
        }

        fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
            let main_gate_config = MainGate::<F>::configure(meta);
            TestCircuitConfig { main_gate_config }
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<F>,
        ) -> Result<(), Error> {
            let main_gate = MainGate::<F> {
                config: config.main_gate_config,
                _marker: PhantomData,
            };

            layouter.assign_region(
                || "region 0",
                |mut region| {
                    let offset = &mut 0;
                    let ctx = &mut RegionCtx::new(&mut region, offset);

                    let a = F::from(20u64);
                    let assigned = main_gate.assign_value(ctx, &Some(a).into())?;
                    let assigned_sign = main_gate.sign(ctx, &assigned)?;
                    main_gate.assert_zero(ctx, &assigned_sign.into())?;

                    let a = F::from(21u64);
                    let assigned = main_gate.assign_value(ctx, &Some(a).into())?;
                    let assigned_sign = main_gate.sign(ctx, &assigned)?;
                    main_gate.assert_one(ctx, &assigned_sign.into())?;

                    Ok(())
                },
            )?;

            Ok(())
        }
    }

    #[test]
    fn test_main_gate_sign() {
        const K: u32 = 10;
        let circuit = TestCircuitSign::<Fp> {
            _marker: PhantomData::<Fp>,
        };
        let public_inputs = vec![vec![]];
        let prover = match MockProver::run(K, &circuit, public_inputs) {
            Ok(prover) => prover,
            Err(e) => panic!("{:#?}", e),
        };
        assert_eq!(prover.verify(), Ok(()));
    }
}
