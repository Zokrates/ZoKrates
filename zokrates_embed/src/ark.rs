use ark_bls12_377::{
    constraints::PairingVar as BLS12PairingVar, Bls12_377 as BLS12PairingEngine, Fq as BLS12Fq,
    Fq2 as BLS12Fq2,
};
use ark_bw6_761::Fr as BW6Fr;
use ark_ec::PairingEngine;
use ark_ff::{BigInteger, One, PrimeField};
use ark_r1cs_std::bits::boolean::Boolean;
use ark_relations::{
    ns,
    r1cs::{ConstraintSystem, ConstraintSystemRef},
};

use ark_crypto_primitives::snark::constraints::SNARKGadget;
use ark_gm17::{constraints::GM17VerifierGadget, Proof, VerifyingKey, GM17};
use ark_r1cs_std::alloc::{AllocVar, AllocationMode};

use crate::Constraint;
use ark_crypto_primitives::SNARK;
use ark_r1cs_std::fields::fp::FpVar;
use ark_r1cs_std::ToBitsGadget;
use ark_relations::r1cs::{ConstraintSynthesizer, SynthesisError};
use ark_std::test_rng;
use std::str::FromStr;
use zokrates_field::Field;

type GM17Snark = GM17<BLS12PairingEngine>;
type VerifierGadget = GM17VerifierGadget<BLS12PairingEngine, BLS12PairingVar>;

type G1 = <ark_ec::bls12::Bls12<ark_bls12_377::Parameters> as PairingEngine>::G1Affine;
type G2 = <ark_ec::bls12::Bls12<ark_bls12_377::Parameters> as PairingEngine>::G2Affine;

macro_rules! var {
    ($f:expr, $offset:expr) => {
        match $f {
            FpVar::Var(ref fp) => {
                let var = &fp.variable;
                var.get_index_unchecked($offset).unwrap()
            }
            _ => unreachable!("expected variable, found constant"),
        }
    };
}

macro_rules! g1 {
    ($e:expr, $i0:expr, $i1:expr) => {
        G1::new(
            BLS12Fq::from_str(&*$e[$i0].to_dec_string()).unwrap(),
            BLS12Fq::from_str(&*$e[$i1].to_dec_string()).unwrap(),
            false,
        )
    };
}

macro_rules! g2 {
    ($e:expr, $i0:expr, $i1:expr, $i2:expr, $i3:expr) => {
        G2::new(
            BLS12Fq2::new(
                BLS12Fq::from_str(&*$e[$i0].to_dec_string()).unwrap(),
                BLS12Fq::from_str(&*$e[$i1].to_dec_string()).unwrap(),
            ),
            BLS12Fq2::new(
                BLS12Fq::from_str(&*$e[$i2].to_dec_string()).unwrap(),
                BLS12Fq::from_str(&*$e[$i3].to_dec_string()).unwrap(),
            ),
            false,
        )
    };
}

#[derive(Copy, Clone)]
struct DefaultCircuit {
    pub public_input_size: usize,
}

impl<F: PrimeField> ConstraintSynthesizer<F> for DefaultCircuit {
    fn generate_constraints(self, cs: ConstraintSystemRef<F>) -> Result<(), SynthesisError> {
        for _ in 0..self.public_input_size {
            let _ = FpVar::<F>::new_input(ns!(cs, "alloc_input"), || Ok(F::one()))?;
        }
        Ok(())
    }
}

#[allow(clippy::type_complexity)]
pub fn generate_verify_constraints(
    public_input_size: usize,
) -> (
    usize,
    Vec<usize>,
    Vec<usize>,
    Vec<usize>,
    Vec<Constraint<BW6Fr>>,
    usize,
) {
    let cs_sys = ConstraintSystem::<BW6Fr>::new();
    let cs = ConstraintSystemRef::new(cs_sys);

    let mut rng = test_rng();
    let circuit = DefaultCircuit { public_input_size };

    let (pk, vk) = GM17Snark::circuit_specific_setup(circuit, &mut rng).unwrap();
    let proof = GM17Snark::prove(&pk, circuit, &mut rng).unwrap();

    let mut fp_vars = Vec::new();
    for _ in 0..public_input_size {
        let fp = FpVar::new_input(ns!(cs, "alloc_input"), || Ok(BLS12Fq::one())).unwrap();
        fp_vars.push(fp);
    }

    let input_booleans: Vec<Vec<Boolean<_>>> =
        fp_vars.iter().map(|i| i.to_bits_le().unwrap()).collect();

    let inputs = <VerifierGadget as SNARKGadget<
        <BLS12PairingEngine as PairingEngine>::Fr,
        <BLS12PairingEngine as PairingEngine>::Fq,
        GM17Snark,
    >>::InputVar::new(input_booleans);

    let proof = <VerifierGadget as SNARKGadget<
        <BLS12PairingEngine as PairingEngine>::Fr,
        <BLS12PairingEngine as PairingEngine>::Fq,
        GM17Snark,
    >>::new_proof_unchecked(
        ns!(cs, "alloc_proof"),
        || Ok(proof),
        AllocationMode::Witness,
    )
    .unwrap();

    let vk = <VerifierGadget as SNARKGadget<
        <BLS12PairingEngine as PairingEngine>::Fr,
        <BLS12PairingEngine as PairingEngine>::Fq,
        GM17Snark,
    >>::new_verification_key_unchecked(
        ns!(cs, "alloc_vk"), || Ok(vk), AllocationMode::Witness
    )
    .unwrap();

    let res = <VerifierGadget as SNARKGadget<
        <BLS12PairingEngine as PairingEngine>::Fr,
        <BLS12PairingEngine as PairingEngine>::Fq,
        GM17Snark,
    >>::verify(&vk, &inputs, &proof)
    .unwrap();

    cs.finalize();

    let num_instance_variables = cs.num_instance_variables();
    let input_indices = fp_vars.iter().map(|f| var!(f, 0)).collect::<Vec<usize>>();

    let proof_indices: Vec<usize> = vec![
        var!(proof.a.x, num_instance_variables),
        var!(proof.a.y, num_instance_variables),
        var!(proof.b.x.c0, num_instance_variables),
        var!(proof.b.x.c1, num_instance_variables),
        var!(proof.b.y.c0, num_instance_variables),
        var!(proof.b.y.c1, num_instance_variables),
        var!(proof.c.x, num_instance_variables),
        var!(proof.c.y, num_instance_variables),
    ];

    let mut vk_indices: Vec<usize> = vec![
        var!(vk.h_g2.x.c0, num_instance_variables),
        var!(vk.h_g2.x.c1, num_instance_variables),
        var!(vk.h_g2.y.c0, num_instance_variables),
        var!(vk.h_g2.y.c1, num_instance_variables),
        var!(vk.g_alpha_g1.x, num_instance_variables),
        var!(vk.g_alpha_g1.y, num_instance_variables),
        var!(vk.h_beta_g2.x.c0, num_instance_variables),
        var!(vk.h_beta_g2.x.c1, num_instance_variables),
        var!(vk.h_beta_g2.y.c0, num_instance_variables),
        var!(vk.h_beta_g2.y.c1, num_instance_variables),
        var!(vk.g_gamma_g1.x, num_instance_variables),
        var!(vk.g_gamma_g1.y, num_instance_variables),
        var!(vk.h_gamma_g2.x.c0, num_instance_variables),
        var!(vk.h_gamma_g2.x.c1, num_instance_variables),
        var!(vk.h_gamma_g2.y.c0, num_instance_variables),
        var!(vk.h_gamma_g2.y.c1, num_instance_variables),
    ];

    vk_indices.extend(
        vk.query
            .iter()
            .map(|q| {
                vec![
                    var!(q.x, num_instance_variables),
                    var!(q.y, num_instance_variables),
                ]
            })
            .flatten(),
    );

    let out_index = match &res {
        Boolean::Is(x) => x
            .variable()
            .get_index_unchecked(num_instance_variables)
            .unwrap(),
        Boolean::Not(x) => x
            .variable()
            .get_index_unchecked(num_instance_variables)
            .unwrap(),
        _ => unreachable!(),
    };

    let matrices = cs.to_matrices().unwrap();
    let constraints: Vec<Constraint<_>> = matrices
        .a
        .into_iter()
        .zip(matrices.b.into_iter())
        .zip(matrices.c.into_iter())
        .map(|((a, b), c)| Constraint {
            a: a.into_iter().map(|(f, index)| (index, f)).collect(),
            b: b.into_iter().map(|(f, index)| (index, f)).collect(),
            c: c.into_iter().map(|(f, index)| (index, f)).collect(),
        })
        .collect();

    (
        out_index,
        input_indices,
        proof_indices,
        vk_indices,
        constraints,
        cs.num_witness_variables() + cs.num_instance_variables(),
    )
}

pub fn generate_verify_witness<T: Field>(inputs: &[T], proof: &[T], vk: &[T]) -> Vec<T> {
    assert_eq!(proof.len(), 8);
    assert_eq!(vk.len(), 18 + (2 * inputs.len()));

    let cs_sys = ConstraintSystem::<BW6Fr>::new();
    let cs = ConstraintSystemRef::new(cs_sys);

    let mut fp_vars = Vec::new();
    for input in inputs {
        let input_field: BLS12Fq = BLS12Fq::from_str(input.to_dec_string().as_str()).unwrap();
        let fp = FpVar::new_input(ns!(cs, "alloc_input"), || Ok(input_field)).unwrap();
        fp_vars.push(fp);
    }

    let input_booleans: Vec<Vec<Boolean<_>>> = fp_vars
        .into_iter()
        .map(|i| i.to_bits_le().unwrap())
        .collect();

    let inputs = <VerifierGadget as SNARKGadget<
        <BLS12PairingEngine as PairingEngine>::Fr,
        <BLS12PairingEngine as PairingEngine>::Fq,
        GM17Snark,
    >>::InputVar::new(input_booleans);

    let proof = <VerifierGadget as SNARKGadget<
        <BLS12PairingEngine as PairingEngine>::Fr,
        <BLS12PairingEngine as PairingEngine>::Fq,
        GM17Snark,
    >>::new_proof_unchecked(
        ns!(cs, "alloc_proof"),
        || {
            Ok(Proof {
                a: g1!(proof, 0, 1),
                b: g2!(proof, 2, 3, 4, 5),
                c: g1!(proof, 6, 7),
            })
        },
        AllocationMode::Witness,
    )
    .unwrap();

    let vk = <VerifierGadget as SNARKGadget<
        <BLS12PairingEngine as PairingEngine>::Fr,
        <BLS12PairingEngine as PairingEngine>::Fq,
        GM17Snark,
    >>::new_verification_key_unchecked(
        ns!(cs, "alloc_vk"),
        || {
            Ok(VerifyingKey {
                h_g2: g2!(vk, 0, 1, 2, 3),
                g_alpha_g1: g1!(vk, 4, 5),
                h_beta_g2: g2!(vk, 6, 7, 8, 9),
                g_gamma_g1: g1!(vk, 10, 11),
                h_gamma_g2: g2!(vk, 12, 13, 14, 15),
                query: (16..vk.len())
                    .collect::<Vec<_>>()
                    .chunks(2)
                    .map(|c| g1!(vk, c[0], c[1]))
                    .collect(),
            })
        },
        AllocationMode::Witness,
    )
    .unwrap();

    let _ = <VerifierGadget as SNARKGadget<
        <BLS12PairingEngine as PairingEngine>::Fr,
        <BLS12PairingEngine as PairingEngine>::Fq,
        GM17Snark,
    >>::verify(&vk, &inputs, &proof)
    .unwrap();

    cs.finalize();

    let cs = cs.borrow().unwrap();
    let witness_variables: Vec<BLS12Fq> = cs.witness_assignment.clone();

    cs.instance_assignment
        .clone()
        .into_iter()
        .chain(witness_variables)
        .map(|fq| T::from_byte_vector(fq.into_repr().to_bytes_le()))
        .collect()
}
//
// #[test]
// fn generate_verify_constraints_test() {
//     let _ = generate_verify_constraints(0);
//     let _ = generate_verify_constraints(1);
//     let _ = generate_verify_constraints(2);
//     let _ = generate_verify_constraints(3);
// }
//
// #[test]
// fn generate_verify_witness_test() {
//     let inputs = [Bw6_761Field::try_from_dec_str("1").unwrap()];
//
//     let proof = [
//         Bw6_761Field::try_from_dec_str("235782943111137747530705097136902819013408845361203175534778158383169533838434449255860464757085033350571842898348").unwrap(),
//         Bw6_761Field::try_from_dec_str("165331200638255581426424843336405231597247782079004588915091938378328147868982661937191476394972887856514105171163").unwrap(),
//         Bw6_761Field::try_from_dec_str("254232159831445544309193578749463370103753380550537149146142458926739764205591902671028001365299904981732549136683").unwrap(),
//         Bw6_761Field::try_from_dec_str("110312323157092528819028093312347351137226193437841103950521979205975893813298913605994406937897967164905526329").unwrap(),
//         Bw6_761Field::try_from_dec_str("92280397906394491698354903378414754820599196865399227396875767801540756083841866092570985429394716805577869077320").unwrap(),
//         Bw6_761Field::try_from_dec_str("222376854776830339884944565405903085055220167393343147071200792467030923517478950522963886729324485932937864818308").unwrap(),
//         Bw6_761Field::try_from_dec_str("166743706972793452960182372942649700997661741034432782404177255897479938072993375303879840122831003023380175217916").unwrap(),
//         Bw6_761Field::try_from_dec_str("18241406009053346360181174307452353181071423946478108185071609940159980631851949302336828153867681522722723293022").unwrap()
//     ];
//
//     let vk = [
//         Bw6_761Field::try_from_dec_str("195958723741148274853455159201485888818691815489993268749601350896046313859202060813450393651648043990458085546444").unwrap(),
//         Bw6_761Field::try_from_dec_str("250586460666268137658218641890677997621978277070882765940531847948228319942427751723561925927172535045539183567512").unwrap(),
//         Bw6_761Field::try_from_dec_str("57234023875145056535872139814081896160035766307948448121984762577416591136138301518701641437360482429441983035003").unwrap(),
//         Bw6_761Field::try_from_dec_str("121354278543550641612200697783815693391285241292446633969973883979058168011709728550967337052029015353984616443838").unwrap(),
//         Bw6_761Field::try_from_dec_str("135646801808269634260317971016961224255462547427375299328984758093466241297387693004994926726553046102004047340443").unwrap(),
//         Bw6_761Field::try_from_dec_str("195568746810845500554149528092548239960661449012126888654840599195256227437456693344562709998175426801251472283163").unwrap(),
//         Bw6_761Field::try_from_dec_str("76643185476572704963146246347086453256291196504794788777518008941873692890848784834169129586710009695562569789959").unwrap(),
//         Bw6_761Field::try_from_dec_str("14407414746636140435653754439538456360783775597216728853315098252325800116296090722143648811029811922230403987642").unwrap(),
//         Bw6_761Field::try_from_dec_str("241948018763885192315660730393291298686330622866040876232946054588870352441939487336082531324175120194138393276854").unwrap(),
//         Bw6_761Field::try_from_dec_str("216905906087737597184922995184221169940829775146684973188909001659019536927834329277848699472206295867448317914180").unwrap(),
//         Bw6_761Field::try_from_dec_str("127980131940757792489522902422610952616070039736870084796440882268680289963781343048894476650287858658933965223336").unwrap(),
//         Bw6_761Field::try_from_dec_str("169029061244756455288512803317939880636727782082563463287674108474881061361652255168002034068840462861372798016506").unwrap(),
//         Bw6_761Field::try_from_dec_str("195958723741148274853455159201485888818691815489993268749601350896046313859202060813450393651648043990458085546444").unwrap(),
//         Bw6_761Field::try_from_dec_str("250586460666268137658218641890677997621978277070882765940531847948228319942427751723561925927172535045539183567512").unwrap(),
//         Bw6_761Field::try_from_dec_str("57234023875145056535872139814081896160035766307948448121984762577416591136138301518701641437360482429441983035003").unwrap(),
//         Bw6_761Field::try_from_dec_str("121354278543550641612200697783815693391285241292446633969973883979058168011709728550967337052029015353984616443838").unwrap(),
//         Bw6_761Field::try_from_dec_str("32195860399927859397562455120174283256312634316227644355523312506401814372948826718688654459074592342744796675279").unwrap(),
//         Bw6_761Field::try_from_dec_str("166911092056770617566930877485561483108518987792750382293738717177408821285936224491024516087699049333713921575672").unwrap(),
//         Bw6_761Field::try_from_dec_str("196418598772862889574615860540297776905473069168713196436807788640920896318323041466544668158806161593231021557450").unwrap(),
//         Bw6_761Field::try_from_dec_str("225560192455589244304893893333701602605197247902671499720170402331956986544121723047250430395938168862941096435629").unwrap()
//     ];
//
//     let res = generate_verify_witness(&inputs, &proof, &vk);
//     println!("{:?}", res.len());
// }

pub fn from_ark<T: zokrates_field::Field, E: PairingEngine>(c: Constraint<E::Fq>) -> Constraint<T> {
    Constraint {
        a: c.a
            .into_iter()
            .map(|(index, fq)| {
                let mut res: Vec<u8> = vec![];
                fq.into_repr().write_le(&mut res).unwrap();
                (index, T::from_byte_vector(res))
            })
            .collect(),
        b: c.b
            .into_iter()
            .map(|(index, fq)| {
                let mut res: Vec<u8> = vec![];
                fq.into_repr().write_le(&mut res).unwrap();
                (index, T::from_byte_vector(res))
            })
            .collect(),
        c: c.c
            .into_iter()
            .map(|(index, fq)| {
                let mut res: Vec<u8> = vec![];
                fq.into_repr().write_le(&mut res).unwrap();
                (index, T::from_byte_vector(res))
            })
            .collect(),
    }
}
