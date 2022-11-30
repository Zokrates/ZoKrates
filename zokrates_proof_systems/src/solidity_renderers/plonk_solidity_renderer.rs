// Copied and adjusted from:
// https://github.com/matter-labs/solidity_plonk_verifier/blob/master/bellman_vk_codegen/src/lib.rs

use handlebars::*;
use zokrates_field::Field;

use crate::{G1Affine, G2Affine, Scheme};
use serde_json::value::Map;

use crate::Plonk;

pub fn render_verification_key<T: Field>(vk: &<Plonk as Scheme<T>>::VerificationKey) -> String {
    let mut map = Map::new();

    let domain_size = vk.n.next_power_of_two().to_string();
    map.insert("domain_size".to_owned(), to_json(domain_size));

    let num_inputs = vk.num_inputs.to_string();
    map.insert("num_inputs".to_owned(), to_json(num_inputs));

    map.insert("omega".to_owned(), to_json(vk.omega.clone()));

    for (i, c) in vk.selector_commitments.iter().enumerate() {
        let rendered = render_g1_affine_to_hex(&c);

        for j in 0..2 {
            map.insert(
                format!("selector_commitment_{}_{}", i, j),
                to_json(&rendered[j]),
            );
        }
    }

    for (i, c) in vk.next_step_selector_commitments.iter().enumerate() {
        let rendered = render_g1_affine_to_hex(&c);

        for j in 0..2 {
            map.insert(
                format!("next_step_selector_commitment_{}_{}", i, j),
                to_json(&rendered[j]),
            );
        }
    }

    for (i, c) in vk.permutation_commitments.iter().enumerate() {
        let rendered = render_g1_affine_to_hex(&c);

        for j in 0..2 {
            map.insert(
                format!("permutation_commitment_{}_{}", i, j),
                to_json(&rendered[j]),
            );
        }
    }

    for (i, c) in vk.non_residues.iter().enumerate() {
        map.insert(format!("permutation_non_residue_{}", i), to_json(&c));
    }

    let rendered = render_g2_affine_to_hex(&vk.g2_elements[1]);

    map.insert("g2_x_x_c0".to_owned(), to_json(&rendered[0]));
    map.insert("g2_x_x_c1".to_owned(), to_json(&rendered[1]));
    map.insert("g2_x_y_c0".to_owned(), to_json(&rendered[2]));
    map.insert("g2_x_y_c1".to_owned(), to_json(&rendered[3]));

    let mut handlebars = Handlebars::new();

    // register template from a file and assign a name to it
    let template_str = include_str!("../../solidity_templates/PlonkVerifier.sol");
    handlebars
        .register_template_string("contract", &template_str)
        .expect("must read the template");

    // make data and render it
    // println!("{}", handlebars.render("contract", &map).unwrap());

    handlebars.render("contract", &map).unwrap()
}

fn render_g1_affine_to_hex(point: &G1Affine) -> [String; 2] {
    if point.is_infinity {
        return ["0x0".to_owned(), "0x0".to_owned()];
    }

    let point = point.clone();

    [point.x, point.y]
}

fn render_g2_affine_to_hex(point: &G2Affine) -> [String; 4] {
    match point {
        G2Affine::Fq2(point) => {
            if point.is_infinity {
                return [
                    "0x0".to_owned(),
                    "0x0".to_owned(),
                    "0x0".to_owned(),
                    "0x0".to_owned(),
                ];
            }

            let point = point.clone();

            [point.x.0, point.x.1, point.y.0, point.y.1]
        }
        _ => unreachable!(),
    }
}
