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
    let template_str =
        include_str!("../../zokrates_proof_systems/solidity_templates/PlonkVerifier.sol");
    handlebars
        .register_template_string("contract", &template_str)
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
