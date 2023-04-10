mod r1cs;
mod witness;

pub use r1cs::write_r1cs;
pub use witness::write_witness;

#[cfg(test)]
mod tests {
    use std::io::Cursor;

    use bellman_ce::pairing::bn256::Bn256;
    use zkutil::circom_circuit::{
        create_rng, generate_random_parameters, prove, r1cs_from_bin, witness_from_bin,
        CircomCircuit,
    };
    use zokrates_ast::{
        flat::{Parameter, Variable},
        ir::{LinComb, Prog, PublicInputs, QuadComb, Statement, Witness},
    };
    use zokrates_field::Bn128Field;

    use super::*;

    #[test]
    fn setup_and_prove() {
        let prog: Prog<Bn128Field> = Prog {
            module_map: Default::default(),
            arguments: vec![
                Parameter::private(Variable::new(0)),
                Parameter::public(Variable::new(1)),
            ],
            return_count: 1,
            statements: vec![
                Statement::constraint(
                    QuadComb::new(
                        LinComb::from(Variable::new(0)),
                        LinComb::from(Variable::new(0)),
                    ),
                    LinComb::from(Variable::new(0)),
                    None,
                ),
                Statement::constraint(
                    LinComb::from(Variable::new(0)) + LinComb::from(Variable::new(1)),
                    Variable::public(0),
                    None,
                ),
            ],
            solvers: vec![],
        };

        let mut r1cs = vec![];

        write_r1cs(&mut r1cs, prog).unwrap();

        let public_inputs: PublicInputs = vec![Variable::new(1)].into_iter().collect();

        let witness: Witness<Bn128Field> = Witness(
            vec![
                (Variable::new(0), Bn128Field::from(1u32)),
                (Variable::new(1), Bn128Field::from(1u32)),
                (Variable::one(), Bn128Field::from(1u32)),
                (Variable::public(0), Bn128Field::from(2u32)),
            ]
            .into_iter()
            .collect(),
        );

        let mut wtns = vec![];

        write_witness(&mut wtns, witness, public_inputs).unwrap();

        let (r1cs, mapping) = r1cs_from_bin(Cursor::new(r1cs)).unwrap();
        let wtns = witness_from_bin::<Bn256, _>(Cursor::new(wtns)).unwrap();

        let rng = create_rng();
        let circuit = CircomCircuit {
            r1cs: r1cs.clone(),
            witness: None,
            wire_mapping: None,
        };

        let params = generate_random_parameters(circuit, rng).unwrap();

        let circuit = CircomCircuit {
            r1cs,
            witness: Some(wtns),
            wire_mapping: Some(mapping),
        };
        let rng = create_rng();
        assert!(prove(circuit, &params, rng).is_ok());
    }
}
