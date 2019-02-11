extern crate rand;

use bellman::groth16::Proof;
use bellman::groth16::{
    create_random_proof, generate_random_parameters, prepare_verifying_key, verify_proof,
    Parameters, VerifyingKey,
};
use bellman::{Circuit, ConstraintSystem, LinearCombination, SynthesisError, Variable};
use ir::interpreter::Witness;
use ir::*;
use pairing::bn256::{Bn256, Fr};
use std::collections::BTreeMap;
use zokrates_field::field::{Field, FieldPrime};

use self::rand::*;
use flat_absy::FlatVariable;

#[derive(Clone)]
pub struct Computation<T: Field> {
    program: Prog<T>,
    witness: Option<Witness<T>>,
}

impl<T: Field> Computation<T> {
    pub fn with_witness(program: Prog<T>, witness: Witness<T>) -> Self {
        Computation {
            program,
            witness: Some(witness),
        }
    }

    pub fn without_witness(program: Prog<T>) -> Self {
        Computation {
            program,
            witness: None,
        }
    }
}
impl<T: Field> fmt::Display for Computation<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "Compute:\n{}\n\nwith witness {}",
            self.program,
            self.witness
                .clone()
                .unwrap()
                .0
                .iter()
                .map(|(k, v)| format!("{} -> {}", k, v))
                .collect::<Vec<_>>()
                .join("\n"),
        )
    }
}

impl LinComb<FieldPrime> {
    fn into_bellman_combination(
        self,
        symbols: &BTreeMap<FlatVariable, Variable>,
    ) -> LinearCombination<Bn256> {
        self.0
            .into_iter()
            .map(|(k, v)| (Fr::from(v), symbols.get(&k).unwrap().clone()))
            .fold(LinearCombination::zero(), |acc, e| acc + e)
    }
}

fn alloc<CS: ConstraintSystem<Bn256>>(
    cs: &mut CS,
    var: FlatVariable,
    witness: &Witness<FieldPrime>,
) -> Result<Variable, SynthesisError> {
    match var.is_output() {
        true => cs.alloc(
            || format!("{}", var),
            || {
                // let w = witness.ok_or(SynthesisError::AssignmentMissing)?;
                let val = witness
                    .0
                    .get(&var)
                    .ok_or(SynthesisError::AssignmentMissing)?;
                Ok(Fr::from(val.clone()))
            },
        ),
        false => cs.alloc_input(
            || format!("{}", var),
            || {
                // let witness = witness.ok_or(SynthesisError::AssignmentMissing)?;
                let val = witness
                    .0
                    .get(&var)
                    .ok_or(SynthesisError::AssignmentMissing)?;
                Ok(Fr::from(val.clone()))
            },
        ),
    }
}

impl Prog<FieldPrime> {
    pub fn synthesize<CS: ConstraintSystem<Bn256>>(
        self,
        cs: &mut CS,
        witness: Option<Witness<FieldPrime>>,
    ) -> Result<(), SynthesisError> {
        let mut symbols = BTreeMap::new();

        let mut arguments = vec![];

        let witness = witness.unwrap();

        for (index, (var, private)) in self
            .main
            .arguments
            .clone()
            .into_iter()
            .zip(self.private)
            .enumerate()
        {
            let wire = match private {
                true => cs.alloc(
                    || format!("PRIVATE_INPUT_{}", index),
                    || {
                        // let w = witness.ok_or(SynthesisError::AssignmentMissing)?;
                        let val = witness
                            .0
                            .get(&var)
                            .ok_or(SynthesisError::AssignmentMissing)?;
                        Ok(Fr::from(val.clone()))
                    },
                ),
                false => cs.alloc_input(
                    || format!("PUBLIC_INPUT_{}", index),
                    || {
                        // let witness = witness.ok_or(SynthesisError::AssignmentMissing)?;
                        let val = witness
                            .0
                            .get(&var)
                            .ok_or(SynthesisError::AssignmentMissing)?;
                        Ok(Fr::from(val.clone()))
                    },
                ),
            }?;
            arguments.push((var, wire));
        }

        symbols.extend(arguments);

        let main = self.main;
        symbols.insert(FlatVariable::one(), CS::one());

        for statement in main.statements {
            match statement {
                Statement::Constraint(quad, lin) => {
                    if lin.is_assignee(&symbols) {
                        let flat_var = lin.0.iter().next().unwrap().0.clone();
                        let var = alloc(cs, flat_var, &witness)?;
                        symbols.insert(flat_var, var);
                    }
                    cs.enforce(
                        || "Definition",
                        |lc| lc + &quad.left.clone().into_bellman_combination(&symbols),
                        |lc| lc + &quad.right.clone().into_bellman_combination(&symbols),
                        |lc| lc + &lin.into_bellman_combination(&symbols),
                    );
                }
                Statement::Directive(d) => {
                    for output in d.outputs {
                        let var = alloc(cs, output, &witness)?;
                        symbols.insert(output, var);
                    }
                }
            }
        }

        Ok(())
    }
}

impl Computation<FieldPrime> {
    pub fn setup_prove_verify(self) -> Proof<Bn256> {
        // run setup phase
        let params = self.clone().setup();
        let pvk = prepare_verifying_key(&params.vk);

        // generate proof
        let rng = &mut thread_rng();

        let proof = create_random_proof(self.clone(), &params, rng).unwrap();

        // extract public inputs
        let public_inputs: Vec<Fr> = self
            .program
            .main
            .arguments
            .clone()
            .iter()
            .zip(self.program.private.clone())
            .filter(|(_, p)| !p)
            .map(|(a, _)| a)
            .chain(
                self.witness
                    .clone()
                    .unwrap()
                    .0
                    .keys()
                    .filter(|k| k.is_output()),
            )
            .map(|v| self.witness.clone().unwrap().0.get(v).unwrap().clone())
            .map(|v| Fr::from(v.clone()))
            .collect();

        assert!(verify_proof(&pvk, &proof, &public_inputs).unwrap());

        proof
    }

    pub fn setup(self) -> Parameters<Bn256> {
        let rng = &mut thread_rng();
        // run setup phase
        generate_random_parameters(self, rng).unwrap()
    }
}

impl Circuit<Bn256> for Computation<FieldPrime> {
    fn synthesize<CS: ConstraintSystem<Bn256>>(self, cs: &mut CS) -> Result<(), SynthesisError> {
        self.program.synthesize(cs, self.witness)
    }
}

pub fn serialize_vk(vk: VerifyingKey<Bn256>) -> String {
    format!(
        "
vk.alpha = {}
vk.beta = {}
vk.gamma = {}
vk.delta = {}
vk.gammaABC.len() = {}
{}",
        vk.alpha_g1,
        vk.beta_g2,
        vk.gamma_g2,
        vk.delta_g2,
        vk.ic.len(),
        vk.ic
            .iter()
            .enumerate()
            .map(|(i, x)| format!("vk.gammaABC[{}] = {}", i, x))
            .collect::<Vec<_>>()
            .join("\n")
    )
    .replace("G2(x=Fq2(Fq(", "[[")
    .replace("), y=Fq(", ", ")
    .replace("G1(x=Fq(", "[")
    .replace(") + Fq(", ", ")
    .replace("))", "]")
    .replace(") * u), y=Fq2(Fq(", "], [")
    .replace(") * u]", "]]")
}

pub fn serialize_proof(p: Proof<Bn256>) -> String {
    format!(
        "{{
    \"a\": {},
    \"b\": {},
    \"c\": {},
}}",
        p.a, p.b, p.c
    )
    .replace("G2(x=Fq2(Fq(", "[[")
    .replace("), y=Fq(", ", ")
    .replace("G1(x=Fq(", "[")
    .replace(") + Fq(", ", ")
    .replace("))", "]")
    .replace(") * u), y=Fq2(Fq(", "], [")
    .replace(") * u]", "]]")
}

#[cfg(test)]
mod tests {
    use super::*;
    use zokrates_field::field::FieldPrime;

    mod prove {
        use super::*;

        #[test]
        fn empty_program() {
            let program: Prog<FieldPrime> = Prog {
                main: Function {
                    id: String::from("main"),
                    arguments: vec![],
                    returns: vec![],
                    statements: vec![],
                },
                private: vec![],
            };

            let witness = program.clone().execute::<FieldPrime>(&vec![]).unwrap();
            let computation = Computation::with_witness(program, witness);

            let _proof = computation.setup_prove_verify();
        }
    }

    mod serialize {
        use super::*;
        mod vk {
            use super::*;
            #[test]
            fn serialize() {
                let program: Prog<FieldPrime> = Prog {
                    main: Function {
                        id: String::from("main"),
                        arguments: vec![],
                        returns: vec![],
                        statements: vec![],
                    },
                    private: vec![],
                };

                let computation = Computation::with_witness(program, Witness::empty());

                let params = computation.setup();
                println!("{}", serialize_vk(params.vk));
                //                 assert_eq!(serialize_vk(params.vk), "vk.A = [0xe346c6331a8f3b39583944d0812a9ac9be6e507cbae0caea406b46faf05a8f6, 0x8538b02888a72f3415349a24a6493865937bf79facdee21ec725d7d07b9f77e], [0xd6d071f9dc99d9d559a8b2ef4cb28048f402db2c5ccce439b75967f97c1cc62, 0xd82c10002969164b4534f6cbe76d19183ecf4cccc7ec247bbae93f3fcd12737]
                //         vk.B = 0x4fdf8eb48ef7488c914383f1e63a913079e083d4b42714e55bf594c3e8e531f, 0x2e189cec6babb474e475bb86353aa148d09729c643cfaecc7f1e9871f4dd476a
                //         vk.C = [0x2e17f9799ec8dc45c46643cc04b6f572a62451f7745281603abe9bf06dcb258f, 0x1cd480216a68e65fa4c8b595481c61a7fee0c26fa3d54a9d0e520e4c63a3924b], [0x18adf6cc01f7492952f7bc1885ef00e8d4724913ac36746b00e7e50b8c83008e, 0x194c623b624fd5dba6d3d3f510f2fe616deebc153fa2fb5e9a639554454d987d]
                //         vk.gamma = [0x144a4e9398e9b5243f0f9966858948a9e72795c4352a1b574c6ebd46e19c7cb3, 0x259ca428fcc7323d21e64eaa7b2eff9b5df0a9c8f4d590c34b06c5ee25cb2a4b], [0x255e832555526cd59d576a8c6adcdf25a2d9a28ab1dd12891ebb3bf4ca918476, 0x21b0d3078440447b3a1dd437fc61949148d82af0482510350b872cdd3b83073b]
                //         vk.gammaBeta1 = 0x9752a30af0c5550eda78c403f8565be77fea017ffd7813d75583a3ce6b22367, 0xa7996aaf0133388110732201d7ebade0a93946afee0b5a6d07789fece8ce514
                //         vk.gammaBeta2 = [0x1658e036bfd100d130fa69a50d06fb3c003089fe55febe816cf729f35c486ca7, 0x1b58887816825b2a21ca6c61a1d59f84ec48f3e9f9e8c15e780aa2941772672d], [0x577fc24305f3a089acadf047c8b264812e7403f06eaf52eef46b05946e9657, 0x1b80136e8693d8127e1674c986f018c206f0f077f27380a22a8d4315ed1bddf2]
                //         vk.Z = [0x2dc0b7d51c8e879253d7a03c0c21909c9719624896353e720f6c8329b0703a69, 0x1e865831288496134884365c838ffd29293cfd53987e9d1efee899f8741a6613], [0x117929d729dd6a6850fc004547327cca0f35bfae38fbca677e45544a7f80fac0, 0x7f15e5f8624d90efdfb778213810201937e06f6b64ba385d291565d41f31436]
                //         vk.IC.len() = 4
                //         vk.IC[0] = 0x17be3e229f6f31225f8e625a939f4883ee1515d6bd32f6b2f820c151643a7ea8, 0x9fd8bb5948457176ae10d7895ec513bbc6b87a0f30b5d3ed22d1a73cdf87aa
                //         vk.IC[1] = 0x126abf506aa18ab42349c3c81ef2b81efa53178c37b3b59bbf634b8d7c83012, 0x3b03e34fbfbd69e8652aa9bb2a9f3801ef7de3d69f8e77e29f2cdcea9735ace
                //         vk.IC[2] = 0x25eb86c6ff818d3f56cf5c4bfd86152b5fc46f2e9576e3cd215dc2182472dfd9, 0x25c3b07f946bb68ab0cfd50fc2a88d8d3738040e09125d241452aab6b865f986
                //         vk.IC[3] = 0x4952b396f70e1f3ea94f0639375f2824389eb5629e78014a3496937e898f9a5, 0x216c09dc5dd85d771b1088db01f8b3285d33c82ff4363da1b09c81611c31894d
                // ");
            }
        }

        mod proof {
            use super::*;

            #[test]
            fn serialize() {
                let rng = &mut thread_rng();

                let program: Prog<FieldPrime> = Prog {
                    main: Function {
                        id: String::from("main"),
                        arguments: vec![],
                        returns: vec![],
                        statements: vec![],
                    },
                    private: vec![],
                };

                let witness = program.clone().execute::<FieldPrime>(&vec![]).unwrap();
                let computation = Computation::with_witness(program, witness);

                let params = computation.clone().setup();

                let proof = create_random_proof(computation, &params, rng).unwrap();

                println!("{}", serialize_proof(proof));
                //                 assert_eq!(serialize_vk(params.vk), "vk.A = [0xe346c6331a8f3b39583944d0812a9ac9be6e507cbae0caea406b46faf05a8f6, 0x8538b02888a72f3415349a24a6493865937bf79facdee21ec725d7d07b9f77e], [0xd6d071f9dc99d9d559a8b2ef4cb28048f402db2c5ccce439b75967f97c1cc62, 0xd82c10002969164b4534f6cbe76d19183ecf4cccc7ec247bbae93f3fcd12737]
                //         vk.B = 0x4fdf8eb48ef7488c914383f1e63a913079e083d4b42714e55bf594c3e8e531f, 0x2e189cec6babb474e475bb86353aa148d09729c643cfaecc7f1e9871f4dd476a
                //         vk.C = [0x2e17f9799ec8dc45c46643cc04b6f572a62451f7745281603abe9bf06dcb258f, 0x1cd480216a68e65fa4c8b595481c61a7fee0c26fa3d54a9d0e520e4c63a3924b], [0x18adf6cc01f7492952f7bc1885ef00e8d4724913ac36746b00e7e50b8c83008e, 0x194c623b624fd5dba6d3d3f510f2fe616deebc153fa2fb5e9a639554454d987d]
                //         vk.gamma = [0x144a4e9398e9b5243f0f9966858948a9e72795c4352a1b574c6ebd46e19c7cb3, 0x259ca428fcc7323d21e64eaa7b2eff9b5df0a9c8f4d590c34b06c5ee25cb2a4b], [0x255e832555526cd59d576a8c6adcdf25a2d9a28ab1dd12891ebb3bf4ca918476, 0x21b0d3078440447b3a1dd437fc61949148d82af0482510350b872cdd3b83073b]
                //         vk.gammaBeta1 = 0x9752a30af0c5550eda78c403f8565be77fea017ffd7813d75583a3ce6b22367, 0xa7996aaf0133388110732201d7ebade0a93946afee0b5a6d07789fece8ce514
                //         vk.gammaBeta2 = [0x1658e036bfd100d130fa69a50d06fb3c003089fe55febe816cf729f35c486ca7, 0x1b58887816825b2a21ca6c61a1d59f84ec48f3e9f9e8c15e780aa2941772672d], [0x577fc24305f3a089acadf047c8b264812e7403f06eaf52eef46b05946e9657, 0x1b80136e8693d8127e1674c986f018c206f0f077f27380a22a8d4315ed1bddf2]
                //         vk.Z = [0x2dc0b7d51c8e879253d7a03c0c21909c9719624896353e720f6c8329b0703a69, 0x1e865831288496134884365c838ffd29293cfd53987e9d1efee899f8741a6613], [0x117929d729dd6a6850fc004547327cca0f35bfae38fbca677e45544a7f80fac0, 0x7f15e5f8624d90efdfb778213810201937e06f6b64ba385d291565d41f31436]
                //         vk.IC.len() = 4
                //         vk.IC[0] = 0x17be3e229f6f31225f8e625a939f4883ee1515d6bd32f6b2f820c151643a7ea8, 0x9fd8bb5948457176ae10d7895ec513bbc6b87a0f30b5d3ed22d1a73cdf87aa
                //         vk.IC[1] = 0x126abf506aa18ab42349c3c81ef2b81efa53178c37b3b59bbf634b8d7c83012, 0x3b03e34fbfbd69e8652aa9bb2a9f3801ef7de3d69f8e77e29f2cdcea9735ace
                //         vk.IC[2] = 0x25eb86c6ff818d3f56cf5c4bfd86152b5fc46f2e9576e3cd215dc2182472dfd9, 0x25c3b07f946bb68ab0cfd50fc2a88d8d3738040e09125d241452aab6b865f986
                //         vk.IC[3] = 0x4952b396f70e1f3ea94f0639375f2824389eb5629e78014a3496937e898f9a5, 0x216c09dc5dd85d771b1088db01f8b3285d33c82ff4363da1b09c81611c31894d
                // ");
            }
        }
    }
}
