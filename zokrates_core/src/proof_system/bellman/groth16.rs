use bellman::groth16::{
    prepare_verifying_key, verify_proof, Parameters, PreparedVerifyingKey, Proof as BellmanProof,
    VerifyingKey,
};
use ir::{Prog, Witness};
use proof_system::bellman::{parse_fr, parse_g1, parse_g2, Bellman, Computation};
use proof_system::schemes::groth16::{ProofPoints, VerificationKey, G16};
use proof_system::schemes::Scheme;
use proof_system::{Backend, Proof};
use zokrates_field::{BellmanFieldExtensions, Field};

const G16_WARNING: &str = "WARNING: You are using the G16 scheme which is subject to malleability. See zokrates.github.io/reference/proving_schemes.html#g16-malleability for implications.";

impl<T: Field + BellmanFieldExtensions> Backend<T, G16> for Bellman {
    fn setup(
        prog: Prog<T>,
    ) -> (
        <G16 as Scheme<T>>::ProvingKey,
        <G16 as Scheme<T>>::VerificationKey,
    ) {
        #[cfg(not(target_arch = "wasm32"))]
        std::env::set_var("BELLMAN_VERBOSE", "0");
        println!("{}", G16_WARNING);

        let parameters = Computation::without_witness(prog).setup();

        let mut pk: Vec<u8> = Vec::new();
        let mut vk_raw: Vec<u8> = Vec::new();

        parameters.write(&mut pk).unwrap();
        parameters.vk.write(&mut vk_raw).unwrap();

        let vk = VerificationKey {
            alpha: parse_g1::<T>(&parameters.vk.alpha_g1),
            beta: parse_g2::<T>(&parameters.vk.beta_g2),
            gamma: parse_g2::<T>(&parameters.vk.gamma_g2),
            delta: parse_g2::<T>(&parameters.vk.delta_g2),
            gamma_abc: parameters
                .vk
                .ic
                .iter()
                .map(|g1| parse_g1::<T>(g1))
                .collect(),
            raw: hex::encode(vk_raw),
        };

        (pk, vk)
    }

    fn generate_proof(
        program: Prog<T>,
        witness: Witness<T>,
        proving_key: <G16 as Scheme<T>>::ProvingKey,
    ) -> Proof<<G16 as Scheme<T>>::ProofPoints> {
        #[cfg(not(target_arch = "wasm32"))]
        std::env::set_var("BELLMAN_VERBOSE", "0");
        println!("{}", G16_WARNING);

        let computation = Computation::with_witness(program, witness);
        let params = Parameters::read(proving_key.as_slice(), true).unwrap();

        let proof = computation.clone().prove(&params);
        let proof_points = ProofPoints {
            a: parse_g1::<T>(&proof.a),
            b: parse_g2::<T>(&proof.b),
            c: parse_g1::<T>(&proof.c),
        };

        let inputs = computation
            .public_inputs_values()
            .iter()
            .map(parse_fr::<T>)
            .collect::<Vec<_>>();

        let mut raw: Vec<u8> = Vec::new();
        proof.write(&mut raw).unwrap();

        Proof::new(proof_points, inputs, hex::encode(&raw))
    }

    fn verify(
        vk: <G16 as Scheme<T>>::VerificationKey,
        proof: Proof<<G16 as Scheme<T>>::ProofPoints>,
    ) -> bool {
        let vk_raw = hex::decode(vk.raw.clone()).unwrap();
        let proof_raw = hex::decode(proof.raw.clone()).unwrap();

        let vk: VerifyingKey<T::BellmanEngine> = VerifyingKey::read(vk_raw.as_slice()).unwrap();
        let pvk: PreparedVerifyingKey<T::BellmanEngine> = prepare_verifying_key(&vk);

        let bellman_proof: BellmanProof<T::BellmanEngine> =
            BellmanProof::read(proof_raw.as_slice()).unwrap();

        let public_inputs: Vec<_> = proof
            .inputs
            .iter()
            .map(|s| {
                T::try_from_str(s.trim_start_matches("0x"), 16)
                    .expect(format!("Invalid {} value: {}", T::name(), s).as_str())
                    .into_bellman()
            })
            .collect::<Vec<_>>();

        verify_proof(&pvk, &bellman_proof, &public_inputs).unwrap_or(false)
    }
}

#[cfg(test)]
mod tests {
    use crate::flat_absy::FlatVariable;
    use crate::ir::{Function, Interpreter, Prog, Statement};
    use proof_system::bellman::Bellman;
    use proof_system::schemes::groth16::G16;
    use proof_system::Backend;
    use zokrates_field::Bn128Field;

    #[test]
    fn verify() {
        let program: Prog<Bn128Field> = Prog {
            main: Function {
                id: String::from("main"),
                arguments: vec![FlatVariable::new(0)],
                returns: vec![FlatVariable::public(0)],
                statements: vec![Statement::Constraint(
                    FlatVariable::new(0).into(),
                    FlatVariable::public(0).into(),
                )],
            },
            private: vec![false],
        };

        let keypair = Bellman::setup(program.clone());
        let interpreter = Interpreter::default();

        let witness = interpreter
            .execute(&program, &vec![Bn128Field::from(42)])
            .unwrap();

        let proof = Bellman::generate_proof(program, witness, keypair.0);
        let ans = <Bellman as Backend<Bn128Field, G16>>::verify(keypair.1, proof);

        assert!(ans);
    }
}
