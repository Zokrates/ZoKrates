// Copied and adjusted from:
// https://github.com/matter-labs/solidity_plonk_verifier/blob/master/bellman_vk_codegen/src/lib.rs

use bellman::pairing::bn256::{Bn256, Fr};
use bellman::pairing::ff::{PrimeField, PrimeFieldRepr};
use bellman::pairing::{CurveAffine, Engine};
use bellman::plonk::better_cs::cs::PlonkCsWidth4WithNextStepParams;
use bellman::plonk::better_cs::keys::{Proof, VerificationKey};

use handlebars::*;

use serde_json::value::Map;

use web3::types::U256;

pub fn render_verification_key(
    vk: &VerificationKey<Bn256, PlonkCsWidth4WithNextStepParams>,
) -> String {
    let mut map = Map::new();

    let domain_size = vk.n.next_power_of_two().to_string();
    map.insert("domain_size".to_owned(), to_json(domain_size));

    let num_inputs = vk.num_inputs.to_string();
    map.insert("num_inputs".to_owned(), to_json(num_inputs));

    let domain =
        bellman::plonk::domains::Domain::<Fr>::new_for_size(vk.n.next_power_of_two() as u64)
            .unwrap();
    let omega = domain.generator;
    map.insert("omega".to_owned(), to_json(render_scalar_to_hex(&omega)));

    for (i, c) in vk.selector_commitments.iter().enumerate() {
        let rendered = render_g1_affine_to_hex::<Bn256>(&c);

        for j in 0..2 {
            map.insert(
                format!("selector_commitment_{}_{}", i, j),
                to_json(&rendered[j]),
            );
        }
    }

    for (i, c) in vk.next_step_selector_commitments.iter().enumerate() {
        let rendered = render_g1_affine_to_hex::<Bn256>(&c);

        for j in 0..2 {
            map.insert(
                format!("next_step_selector_commitment_{}_{}", i, j),
                to_json(&rendered[j]),
            );
        }
    }

    for (i, c) in vk.permutation_commitments.iter().enumerate() {
        let rendered = render_g1_affine_to_hex::<Bn256>(&c);

        for j in 0..2 {
            map.insert(
                format!("permutation_commitment_{}_{}", i, j),
                to_json(&rendered[j]),
            );
        }
    }

    for (i, c) in vk.non_residues.iter().enumerate() {
        let rendered = render_scalar_to_hex::<Fr>(&c);

        map.insert(format!("permutation_non_residue_{}", i), to_json(&rendered));
    }

    let rendered = render_g2_affine_to_hex(&vk.g2_elements[1]);

    map.insert("g2_x_x_c0".to_owned(), to_json(&rendered[0]));
    map.insert("g2_x_x_c1".to_owned(), to_json(&rendered[1]));
    map.insert("g2_x_y_c0".to_owned(), to_json(&rendered[2]));
    map.insert("g2_x_y_c1".to_owned(), to_json(&rendered[3]));

    let mut handlebars = Handlebars::new();

    // register template from a file and assign a name to it
    handlebars
        .register_template_file("contract", "/Users/georg/coding/zoKrates-georg/zokrates_proof_systems/solidity_templates/PlonkVerifier.sol")
        .expect("must read the template");

    // make data and render it
    // println!("{}", handlebars.render("contract", &map).unwrap());

    handlebars.render("contract", &map).unwrap()
}

fn render_scalar_to_hex<F: PrimeField>(el: &F) -> String {
    let mut buff = vec![];
    let repr = el.into_repr();
    repr.write_be(&mut buff).unwrap();

    format!("0x{}", hex::encode(buff))
}

fn render_g1_affine_to_hex<E: Engine>(point: &E::G1Affine) -> [String; 2] {
    if point.is_zero() {
        return ["0x0".to_owned(), "0x0".to_owned()];
    }

    let (x, y) = point.into_xy_unchecked();
    [render_scalar_to_hex(&x), render_scalar_to_hex(&y)]
}

fn render_g2_affine_to_hex(point: &<Bn256 as Engine>::G2Affine) -> [String; 4] {
    if point.is_zero() {
        return [
            "0x0".to_owned(),
            "0x0".to_owned(),
            "0x0".to_owned(),
            "0x0".to_owned(),
        ];
    }

    let (x, y) = point.into_xy_unchecked();

    [
        render_scalar_to_hex(&x.c0),
        render_scalar_to_hex(&x.c1),
        render_scalar_to_hex(&y.c0),
        render_scalar_to_hex(&y.c1),
    ]
}

fn serialize_g1_for_ethereum(point: &<Bn256 as Engine>::G1Affine) -> (U256, U256) {
    if point.is_zero() {
        return (U256::zero(), U256::zero());
    }
    let uncompressed = point.into_uncompressed();

    let uncompressed_slice = uncompressed.as_ref();

    // bellman serializes points as big endian and in the form x, y
    // ethereum expects the same order in memory
    let x = U256::from_big_endian(&uncompressed_slice[0..32]);
    let y = U256::from_big_endian(&uncompressed_slice[32..64]);

    (x, y)
}

fn serialize_fe_for_ethereum(field_element: &Fr) -> U256 {
    let mut be_bytes = [0u8; 32];
    field_element
        .into_repr()
        .write_be(&mut be_bytes[..])
        .expect("get new root BE bytes");
    U256::from_big_endian(&be_bytes[..])
}

pub fn serialize_proof(
    proof: &Proof<Bn256, PlonkCsWidth4WithNextStepParams>,
) -> (Vec<U256>, Vec<U256>) {
    let mut inputs = vec![];
    for input in proof.input_values.iter() {
        inputs.push(serialize_fe_for_ethereum(&input));
    }
    let mut serialized_proof = vec![];

    for c in proof.wire_commitments.iter() {
        let (x, y) = serialize_g1_for_ethereum(&c);
        serialized_proof.push(x);
        serialized_proof.push(y);
    }

    let (x, y) = serialize_g1_for_ethereum(&proof.grand_product_commitment);
    serialized_proof.push(x);
    serialized_proof.push(y);

    for c in proof.quotient_poly_commitments.iter() {
        let (x, y) = serialize_g1_for_ethereum(&c);
        serialized_proof.push(x);
        serialized_proof.push(y);
    }

    for c in proof.wire_values_at_z.iter() {
        serialized_proof.push(serialize_fe_for_ethereum(&c));
    }

    for c in proof.wire_values_at_z_omega.iter() {
        serialized_proof.push(serialize_fe_for_ethereum(&c));
    }

    serialized_proof.push(serialize_fe_for_ethereum(&proof.grand_product_at_z_omega));
    serialized_proof.push(serialize_fe_for_ethereum(&proof.quotient_polynomial_at_z));
    serialized_proof.push(serialize_fe_for_ethereum(
        &proof.linearization_polynomial_at_z,
    ));

    for c in proof.permutation_polynomials_at_z.iter() {
        serialized_proof.push(serialize_fe_for_ethereum(&c));
    }

    let (x, y) = serialize_g1_for_ethereum(&proof.opening_at_z_proof);
    serialized_proof.push(x);
    serialized_proof.push(y);

    let (x, y) = serialize_g1_for_ethereum(&proof.opening_at_z_omega_proof);
    serialized_proof.push(x);
    serialized_proof.push(y);

    (inputs, serialized_proof)
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn render_key() {
        let mut reader = std::io::BufReader::with_capacity(
            1 << 24,
            std::fs::File::open("./deposit_vk.key").unwrap(),
        );
        let vk =
            VerificationKey::<Bn256, PlonkCsWidth4WithNextStepParams>::read(&mut reader).unwrap();
        render_verification_key(&vk, "../Verifier.sol");
    }

    #[test]
    fn render_simple_deposit_key_and_proof() {
        let mut reader = std::io::BufReader::with_capacity(
            1 << 24,
            std::fs::File::open("./deposit_vk.key").unwrap(),
        );
        let vk =
            VerificationKey::<Bn256, PlonkCsWidth4WithNextStepParams>::read(&mut reader).unwrap();
        render_verification_key(&vk, "./test.sol");

        let mut reader = std::io::BufReader::with_capacity(
            1 << 24,
            std::fs::File::open("./deposit_proof.proof").unwrap(),
        );
        let proof = Proof::<Bn256, PlonkCsWidth4WithNextStepParams>::read(&mut reader).unwrap();
        let (inputs, proof) = serialize_proof(&proof);

        println!("Inputs");
        let mut vec = vec![];
        for i in inputs.into_iter() {
            vec.push(format!("\"{}\"", i));
        }
        println!("[{}]", vec.join(","));

        println!("Proof");
        let mut vec = vec![];
        for i in proof.into_iter() {
            vec.push(format!("\"{}\"", i));
        }

        println!("[{}]", vec.join(","));
    }

    #[test]
    fn render_simple_xor_key_and_proof() {
        let mut reader = std::io::BufReader::with_capacity(
            1 << 24,
            std::fs::File::open("./xor_vk.key").unwrap(),
        );
        let vk =
            VerificationKey::<Bn256, PlonkCsWidth4WithNextStepParams>::read(&mut reader).unwrap();
        render_verification_key(&vk, "./xor.sol");

        let mut reader = std::io::BufReader::with_capacity(
            1 << 24,
            std::fs::File::open("./xor_proof.proof").unwrap(),
        );
        let proof = Proof::<Bn256, PlonkCsWidth4WithNextStepParams>::read(&mut reader).unwrap();
        let (inputs, proof) = serialize_proof(&proof);

        println!("Inputs");
        let mut vec = vec![];
        for i in inputs.into_iter() {
            vec.push(format!("\"{}\"", i));
        }
        println!("[{}]", vec.join(","));

        println!("Proof");
        let mut vec = vec![];
        for i in proof.into_iter() {
            vec.push(format!("\"{}\"", i));
        }

        println!("Proof len = {}", vec.len());

        println!("[{}]", vec.join(","));
    }
}
