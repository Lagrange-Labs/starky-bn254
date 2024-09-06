use std::marker::PhantomData;

use ark_bn254::Fq;
use itertools::Itertools;
use num_bigint::BigUint;
use plonky2::{
    field::extension::Extendable,
    hash::hash_types::RichField,
    iop::{
        generator::{GeneratedValues, SimpleGenerator},
        target::Target,
        witness::{PartialWitness, PartitionWitness},
    },
    plonk::circuit_data::CommonCircuitData,
    plonk::{
        circuit_builder::CircuitBuilder,
        config::{AlgebraicHasher, GenericConfig},
    },
    util::serialization::IoResult,
    util::{serialization::Buffer, timing::TimingTree},
};
use plonky2_bn254::fields::{fq_target::FqTarget, u256_target::U256Target};
use starky::{
    proof::StarkProofWithPublicInputsTarget,
    prover::prove,
    recursive_verifier::{
        add_virtual_stark_proof_with_pis, set_stark_proof_with_pis_target,
        verify_stark_proof_circuit,
    },
    verifier::verify_stark_proof,
};

use crate::fields::fq::exp::{
    num_columns, num_public_inputs, read_fq_exp_io, FqExpStark, FQ_EXP_IO_LEN,
};
use crate::{fields::fq::exp::FqExpIONative, utils::utils::get_u256_biguint};
pub const FQ_EXP_INPUT_LEN: usize = 3 * 8;

#[derive(Clone, Debug)]
pub struct FqExpInput {
    pub x: Fq,
    pub offset: Fq,
    pub exp_val: BigUint,
}

#[derive(Clone, Debug)]
pub struct FqExpInputTarget<F: RichField + Extendable<D>, const D: usize> {
    pub x: FqTarget<F, D>,
    pub offset: FqTarget<F, D>,
    pub exp_val: U256Target<F, D>,
}

impl<F: RichField + Extendable<D>, const D: usize> FqExpInputTarget<F, D> {
    pub fn connect(builder: &mut CircuitBuilder<F, D>, lhs: &Self, rhs: &Self) {
        FqTarget::connect(builder, &lhs.x, &rhs.x);
        FqTarget::connect(builder, &lhs.offset, &rhs.offset);
        U256Target::connect(builder, &lhs.exp_val, &rhs.exp_val);
    }
    pub fn to_vec(&self) -> Vec<Target> {
        self.x
            .to_vec()
            .iter()
            .chain(self.offset.to_vec().iter())
            .chain(self.exp_val.to_vec().iter())
            .cloned()
            .collect_vec()
    }
    pub fn from_vec(builder: &mut CircuitBuilder<F, D>, input: &[Target]) -> Self {
        assert!(input.len() == FQ_EXP_INPUT_LEN);
        let num_limbs = 8;
        let mut input = input.to_vec();
        let x_raw = input.drain(0..num_limbs).collect_vec();
        let offset_raw = input.drain(0..num_limbs).collect_vec();
        let exp_val_raw = input.drain(0..num_limbs).collect_vec();
        assert_eq!(input.len(), 0);

        let x = FqTarget::from_vec(builder, &x_raw);
        let offset = FqTarget::from_vec(builder, &offset_raw);
        let exp_val = U256Target::from_vec(&exp_val_raw);
        Self { x, offset, exp_val }
    }

    pub fn set_witness(&self, pw: &mut PartialWitness<F>, value: &FqExpInput) {
        self.x.set_witness(pw, &value.x);
        self.offset.set_witness(pw, &value.offset);
        self.exp_val.set_witness(pw, &value.exp_val);
    }
}

#[cfg(test)]
mod tests {

    use ark_bn254::Fq;

    use ark_ff::Field;
    use ark_std::UniformRand;
    use itertools::Itertools;

    use plonky2::{
        field::goldilocks_field::GoldilocksField,
        iop::witness::PartialWitness,
        plonk::{
            circuit_builder::CircuitBuilder, circuit_data::CircuitConfig,
            config::PoseidonGoldilocksConfig,
        },
    };
    use plonky2_bn254::fields::{fq_target::FqTarget, u256_target::U256Target};

    use crate::{
        fields::fq::circuit::{fq_exp_circuit, FqExpInput, FqExpInputTarget},
        utils::{flags::NUM_INPUT_LIMBS, utils::u32_digits_to_biguint},
    };

    #[test]
    fn test_fq_exp_circuit_with_generator() {
        let mut rng = rand::thread_rng();
        type F = GoldilocksField;
        type C = PoseidonGoldilocksConfig;
        const D: usize = 2;
        let num_io = 127;

        let config = CircuitConfig::standard_recursion_config();
        let mut builder = CircuitBuilder::<F, D>::new(config);
        let inputs_t = (0..num_io)
            .map(|_| {
                let x = FqTarget::empty(&mut builder);
                let offset = FqTarget::empty(&mut builder);
                let exp_val = U256Target::empty(&mut builder);
                FqExpInputTarget { x, offset, exp_val }
            })
            .collect_vec();

        let outputs_t = fq_exp_circuit::<F, C, D>(&mut builder, &inputs_t);

        let mut pw = PartialWitness::<F>::new();
        let mut inputs = vec![];
        let mut outputs = vec![];
        for _ in 0..num_io {
            let exp_val: [u32; NUM_INPUT_LIMBS] = rand::random();
            let exp_val_b = u32_digits_to_biguint(&exp_val);
            let x = Fq::rand(&mut rng);
            let offset = Fq::rand(&mut rng);
            let output = x.pow(&exp_val_b.to_u64_digits()) * offset;
            let input = FqExpInput {
                x,
                offset,
                exp_val: exp_val_b,
            };
            inputs.push(input);
            outputs.push(output);
        }

        inputs_t
            .iter()
            .zip(inputs.iter())
            .for_each(|(t, w)| t.set_witness(&mut pw, w));
        outputs_t
            .iter()
            .zip(outputs.iter())
            .for_each(|(t, w)| t.set_witness(&mut pw, w));

        let data = builder.build::<C>();
        let _proof = data.prove(pw).unwrap();
    }
}
