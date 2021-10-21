use crate::proof_system::scheme::{Scheme, UniversalScheme};
use crate::proof_system::solidity::solidity_pairing_lib;
use crate::proof_system::{G1Affine, G2Affine, SolidityCompatibleField, SolidityCompatibleScheme};
use serde::{Deserialize, Serialize};
use zokrates_field::Field;

#[allow(clippy::upper_case_acronyms)]
pub struct Marlin;

#[derive(Serialize, Deserialize)]
pub struct ProofPoints<Fr, G1> {
    pub commitments: Vec<Vec<(G1, Option<G1>)>>,
    pub evaluations: Vec<Fr>,
    pub pc_proof_proof: Vec<(G1, Option<Fr>)>,
    pub pc_proof_evals: Option<Vec<Fr>>,
    pub prover_messages_count: usize,
}

#[derive(Serialize, Deserialize)]
pub struct KZGVerifierKey<G1, G2> {
    /// The generator of G1.
    pub g: G1,
    /// The generator of G1 that is used for making a commitment hiding.
    pub gamma_g: G1,
    /// The generator of G2.
    pub h: G2,
    /// \beta times the above generator of G2.
    pub beta_h: G2,
}

#[derive(Serialize, Deserialize)]
pub struct VerificationKey<G1, G2> {
    // index_info
    pub num_variables: usize,
    pub num_constraints: usize,
    pub num_non_zero: usize,
    pub num_instance_variables: usize,
    // index comms
    pub index_comms: Vec<(G1, Option<G1>)>,
    // verifier key
    pub vk: KZGVerifierKey<G1, G2>,
    pub max_degree: usize,
    pub supported_degree: usize,
    pub degree_bounds_and_shift_powers: Option<Vec<(usize, G1)>>,
}

impl<T: Field> Scheme<T> for Marlin {
    type VerificationKey = VerificationKey<G1Affine, G2Affine>;
    type ProofPoints = ProofPoints<T, G1Affine>;
}

impl<T: Field> UniversalScheme<T> for Marlin {}

impl<T: SolidityCompatibleField> SolidityCompatibleScheme<T> for Marlin {
    fn export_solidity_verifier(vk: <Marlin as Scheme<T>>::VerificationKey) -> String {
        let (mut template_text, solidity_pairing_lib_sans_bn256g2) =
            (String::from(CONTRACT_TEMPLATE), solidity_pairing_lib(true));

        // let vk_regex = Regex::new(r#"(<%vk_[^i%]*%>)"#).unwrap();
        // let vk_gamma_abc_len_regex = Regex::new(r#"(<%vk_gamma_abc_length%>)"#).unwrap();
        // let vk_gamma_abc_repeat_regex = Regex::new(r#"(<%vk_gamma_abc_pts%>)"#).unwrap();
        // let vk_input_len_regex = Regex::new(r#"(<%vk_input_length%>)"#).unwrap();
        // let input_loop = Regex::new(r#"(<%input_loop%>)"#).unwrap();
        // let input_argument = Regex::new(r#"(<%input_argument%>)"#).unwrap();

        // template_text = vk_regex
        //     .replace(template_text.as_str(), vk.alpha.to_string().as_str())
        //     .into_owned();

        // template_text = vk_regex
        //     .replace(template_text.as_str(), vk.beta.to_string().as_str())
        //     .into_owned();

        // template_text = vk_regex
        //     .replace(template_text.as_str(), vk.gamma.to_string().as_str())
        //     .into_owned();

        // template_text = vk_regex
        //     .replace(template_text.as_str(), vk.delta.to_string().as_str())
        //     .into_owned();

        // let gamma_abc_count: usize = vk.gamma_abc.len();
        // template_text = vk_gamma_abc_len_regex
        //     .replace(
        //         template_text.as_str(),
        //         format!("{}", gamma_abc_count).as_str(),
        //     )
        //     .into_owned();

        // template_text = vk_input_len_regex
        //     .replace(
        //         template_text.as_str(),
        //         format!("{}", gamma_abc_count - 1).as_str(),
        //     )
        //     .into_owned();

        // // feed input values only if there are any
        // template_text = if gamma_abc_count > 1 {
        //     input_loop.replace(
        //         template_text.as_str(),
        //         r#"
        // for(uint i = 0; i < input.length; i++){
        //     inputValues[i] = input[i];
        // }"#,
        //     )
        // } else {
        //     input_loop.replace(template_text.as_str(), "")
        // }
        // .to_string();

        // // take input values as argument only if there are any
        // template_text = if gamma_abc_count > 1 {
        //     input_argument.replace(
        //         template_text.as_str(),
        //         format!(", uint[{}] memory input", gamma_abc_count - 1).as_str(),
        //     )
        // } else {
        //     input_argument.replace(template_text.as_str(), "")
        // }
        // .to_string();

        // let mut gamma_abc_repeat_text = String::new();
        // for (i, g1) in vk.gamma_abc.iter().enumerate() {
        //     gamma_abc_repeat_text.push_str(
        //         format!(
        //             "vk.gamma_abc[{}] = Pairing.G1Point({});",
        //             i,
        //             g1.to_string().as_str()
        //         )
        //         .as_str(),
        //     );
        //     if i < gamma_abc_count - 1 {
        //         gamma_abc_repeat_text.push_str("\n        ");
        //     }
        // }

        // template_text = vk_gamma_abc_repeat_regex
        //     .replace(template_text.as_str(), gamma_abc_repeat_text.as_str())
        //     .into_owned();

        // let re = Regex::new(r"(?P<v>0[xX][0-9a-fA-F]{64})").unwrap();
        // template_text = re.replace_all(&template_text, "uint256($v)").to_string();

        format!("{}{}", solidity_pairing_lib_sans_bn256g2, template_text)
    }
}

// srs_hash: 114320149865102442170582471794120740437258980889930408030668998346742015673363
// domain_size_H: 8
// (log_domain_size_H: 3)
// (inverse_domain_size_H: 19152212512859365819465605027100115702479818850364030050735928663253832433665)
// row_com_A
// row_com_B
// row_com_C
// col_com_A
// col_com_B
// col_com_C
// val_com_A
// val_com_B
// val_com_C
// row_times_col_com_A
// row_times_col_com_B
// row_times_col_com_C
// srs_g_bounds1
// srs_g_bounds2
// srs_h1
// srs_hx
// instance_size: 3
// lagrange_basis_loop: loop for Z:0..instance_size
// instance_lagrange_basis.lagrangeZ = [3132863139099767241574169573939912835427114490787820194859047823825704803470,
// 13274704216607947838603559478828352572698223078672003613477407815293017185178,
// 5480675516131560142068676692489009680423026830956210535361748547457086506969];
// r_lincheck1_loop: loop for Z:0..instance_size
// /// r = r + phi_Z (l_Z(beta)) = r + phi[Z] (l_Z0 + l_Z1 beta + l_Z2 beta^2)
// r = addmod( r, mulmod( instance[Z] , addmod( instance_lagrange_basis.lagrangeZ[0],
//     addmod( mulmod( instance_lagrange_basis.lagrangeZ[1], verifier_challenges.beta1, curve_order ),
//             mulmod( instance_lagrange_basis.lagrangeZ[2],
//                 mulmod(verifier_challenges.beta1,verifier_challenges.beta1, curve_order), curve_order)
//             ,curve_order)
//     , curve_order)
// , curve_order), curve_order);
// instance_padded: [instance[0],instance[1], instance[2],0,0,0,0,0] // pad instance up to domain_size_H?

const CONTRACT_TEMPLATE: &str = r#"
contract Marlin_Verify {

    using Pairing for *;
    ///for inverses, could be optimised
    using ECCMath for *;

    /// hardcoded for bn254
    uint256 constant curve_order = 21888242871839275222246405745257275088548364400416034343698204186575808495617;

    /// circuit dependent hash determining srs
    uint256 constant srs_hash = <%srs_hash%>;

    /// witness_length - scaled up to be a power of 2, log_2(witness_length), witness_length^(-1) % curve_order
    uint8 constant domain_size_H = <%domain_size_H%>;
    uint8 constant log_domain_size_H = <%log_domain_size_H%>;
    uint256 constant inverse_domain_size_H = <%inverse_domain_size_H%>;
    /// num_of_constraints - scaled up to be a power of 2, log_2(num_of_constraints), num_of_constraints^(-1) % curve_order
    uint8 constant domain_size_K = <%domain_size_K%>;
    uint8 constant log_domain_size_K = <%log_domain_size_K%>;
    uint256 constant inverse_domain_size_K = <%inverse_domain_size_K%>;

    Pairing.G1Point Identity = Pairing.scalar_mul( Pairing.G1Point(1,2), uint(0));

    /// Circuit dependent commitments to row polynomials, obtained from python code
    Pairing.G1Point row_com_A = Pairing.G1Point(<%row_com_A%>);
    Pairing.G1Point row_com_B = Pairing.G1Point(<%row_com_B%>);
    Pairing.G1Point row_com_C = Pairing.G1Point(<%row_com_C%>);

    /// Circuit dependent commitments to column polynomials, obtained from python code
    Pairing.G1Point col_com_A = Pairing.G1Point(<%col_com_A%>);
    Pairing.G1Point col_com_B = Pairing.G1Point(<%col_com_B%>);
    Pairing.G1Point col_com_C = Pairing.G1Point(<%col_com_C%>);

    /// Circuit dependent commitments to value polynomials, obtained from python code
    Pairing.G1Point val_com_A = Pairing.G1Point(<%val_com_A%>);
    Pairing.G1Point val_com_B = Pairing.G1Point(<%val_com_B%>);
    Pairing.G1Point val_com_C = Pairing.G1Point(<%val_com_C%>);

    /// Circuit dependent commitments to row(X) * col(X)  polynomials, obtained from python code
    Pairing.G1Point row_times_col_com_A = Pairing.G1Point(<%row_times_col_com_A%>);
    Pairing.G1Point row_times_col_com_B = Pairing.G1Point(<%row_times_col_com_B%>);
    Pairing.G1Point row_times_col_com_C = Pairing.G1Point(<%row_times_col_com_C%>);

    /// g^(x^(d - domain_size_H - 2)) where d is the maximum exponent in the aztec setup.
    Pairing.G1Point srs_g_bounds1 = Pairing.G1Point(<%srs_g_bounds1%>);

    /// g^(x^(d - domain_size_K - 2)) where d is the maximum exponent in the aztec setup.
    Pairing.G1Point srs_g_bounds2 = Pairing.G1Point(<%srs_g_bounds2%>);

    /// h in the aztec setup.
    Pairing.G2Point srs_h1 = Pairing.G2Point(<%srs_h1%>);

    /// h^x in the aztec setup.
    Pairing.G2Point srs_hx = Pairing.G2Point(<%srs_hx%>);


    /// Depends on the size of the instance
    struct instance_lagrange_basis_struct {
        uint256[<%instance_size%>] lagrange0;
        uint256[<%instance_size%>] lagrange1;
        uint256[<%instance_size%>] lagrange2;
    } // ZOKRATES NOTE: REPLACE WITH STATIC ARRAY

    /// Depends on the size of the instance
    /// Require lagrange basis such that langrange_i( root_of_unity_H ** i ) = 1 for i = 0, .., instance_size - 1
    function set_instance_lagrange_basis() internal pure returns (instance_lagrange_basis_struct memory instance_lagrange_basis) {
        <%lagrange_basis_loop%>
    }

    /// Form of expmod when exponentiating by a power of 2 modulo curve_order
    /// Could maybe be optimised
    function exponeniate_by_power_of_2(uint256 value, uint8 power_of_2) internal pure returns (uint) {
        for(uint i = 0; i < power_of_2; i++) {
            value = mulmod(value, value, curve_order) ;
        }
        return value;
    }

    /// submod(a,b) = a - b % curve_order
    function submod(uint256 a, uint256 b) internal pure returns (uint) {
        a = addmod(a, curve_order - b, curve_order);
        return a;
    }

    /// This is the main verification function.  Outputs true if it is convinced, false otherwise.
    function verify(
        uint[<%instance_size%>] memory instance,
        uint256[38] memory proof
    )
    public view returns(bool) {

        verifier_challenges_struct memory verifier_challenges  = get_verifier_challenges(instance,proof);

        polys_to_verify_struct memory polys_to_verify = set_polys_to_verify(instance, proof, verifier_challenges);

        /// S[0] = zA * C1^(xi) * C2^(xi^2 z) * RC_A^(xi^3 z^2) * RC_B^(xi^4 z^2) * RC_C^(xi^5 z^2) * C3^(xi^6 z^2)
        ///         * C4a^(xi^7 z^2) * C4b^(xi^8 z^2)  * G3a^(xi^9 z^2) * G3b^(xi^10 z^2)
        ///         * g^(- total_eval) * (g^(x^(d-b2)))^(- xi^10 z^2 g3(beta3)) * (g^(x^(d-b1)))^(- xi^8 z^2 c4(beta3))
        ///         * W0^beta1 * W1^(z * beta2)  * W2^(z^2 * beta3)

        /// total_eval = zA(beta1) + xi^3 z^2 rcA(beta3) + xi^4 z^2 rcB(beta3) + xi^5 z^2 rcC(beta3)
        ///             + xi^7 z^2 c4(beta3) + xi^8 z^2 c4(beta3) + xi^9 z^2 g3(beta3) + xi^10 z^2 g3(beta3)

        /// S[1] = W0 * W1^z * W2^(z^2)

        /// S[0] = zA * C1^(xi) W0^beta1;
        /// S[1] = W0
        /// total_eval = zA(beta1)
        Pairing.G1Point[2] memory S = [polys_to_verify.zA.commitment, Pairing.G1Point(proof[32], proof[33]) ];
        S[0] = Pairing.addition(S[0], Pairing.scalar_mul(polys_to_verify.lincheck1.commitment, verifier_challenges.xi));
        S[0] = Pairing.addition(S[0], Pairing.scalar_mul(Pairing.G1Point(proof[32], proof[33]), verifier_challenges.beta1));
        uint256 total_eval = polys_to_verify.zA.evaluation;


        /// S[0] = S[0] * C2^(xi^2 z)  * W1^(z * beta1)
        /// S[1] = S[1] * W1^z
        /// r = xi^2 z
        uint r = mulmod( mulmod(verifier_challenges.xi, verifier_challenges.xi, curve_order), verifier_challenges.z, curve_order);
        S[0] = Pairing.addition(S[0], Pairing.scalar_mul(polys_to_verify.lincheck2.commitment, r));
        S[0] = Pairing.addition(S[0], Pairing.scalar_mul(Pairing.G1Point(proof[34], proof[35]),
                mulmod( verifier_challenges.beta2, verifier_challenges.z, curve_order ) ) );
        S[1] = Pairing.addition(S[1], Pairing.scalar_mul( Pairing.G1Point(proof[34], proof[35]), verifier_challenges.z ) );


        /// S[0] = S[0] * RC_A^(xi^3 z^2)
        /// total_eval = total_eval + xi^3 z^2 rc_A(beta3)
        /// r = xi^3 z^2
        r = mulmod(r, mulmod(verifier_challenges.xi, verifier_challenges.z, curve_order), curve_order);
        S[0] = Pairing.addition(S[0], Pairing.scalar_mul( polys_to_verify.rc_A.commitment, r) );
        total_eval = addmod(total_eval, mulmod(r,polys_to_verify.rc_A.evaluation, curve_order), curve_order);

        /// S[0] = S[0] * RC_B^(xi^4 z^2)
        /// total_eval = total_eval + xi^4 z^2 rc_B(beta3)
        /// r = xi^4 z^2
        r = mulmod(r, verifier_challenges.xi, curve_order);
        S[0] = Pairing.addition(S[0], Pairing.scalar_mul(polys_to_verify.rc_B.commitment, r));
        total_eval = addmod(total_eval, mulmod(r,polys_to_verify.rc_B.evaluation, curve_order), curve_order);

        /// S[0] = S[0] * RC_C^(xi^5 z^2)
        /// total_eval = total_eval + xi^5 z^2 rc_C(beta3)
        /// r = xi^5 z^2
        r = mulmod(r, verifier_challenges.xi, curve_order);
        S[0] = Pairing.addition(S[0], Pairing.scalar_mul(polys_to_verify.rc_C.commitment, r));
        total_eval = addmod(total_eval, mulmod(r,polys_to_verify.rc_C.evaluation, curve_order), curve_order);

        /// S[0] = S[0] * C3^(xi^6 z^2)
        /// r = xi^6 z^2
        r = mulmod(r, verifier_challenges.xi, curve_order);
        S[0] = Pairing.addition(S[0], Pairing.scalar_mul(polys_to_verify.lincheck3.commitment, r));

        /// S[0] = S[0] * C4a^(xi^7 z^2)
        /// total_eval = total_eval +  xi^7 z^2 c4(beta3)
        /// r = xi^7 z^2
        r = mulmod(r, verifier_challenges.xi, curve_order);
        S[0] = Pairing.addition(S[0], Pairing.scalar_mul(polys_to_verify.g1_and_2.commitment, r));
        total_eval = addmod(total_eval, mulmod(r,polys_to_verify.g1_and_2.evaluation, curve_order), curve_order);

        /// S[0] = S[0] * C4b^(xi^8 z^2) * (g^(x^(d-b1)))^(- xi^8 z^2 c4(beta3))
        /// total_eval = total_eval + xi^8 z^2 c4(beta3)
        /// r = xi^8 z^2
        r = mulmod(r, verifier_challenges.xi, curve_order);
        S[0] = Pairing.addition(S[0], Pairing.scalar_mul(polys_to_verify.g1_and_2_bound.commitment, r));
        S[0] = Pairing.addition(S[0], Pairing.scalar_mul(srs_g_bounds1,
                curve_order - mulmod(r, polys_to_verify.g1_and_2_bound.evaluation, curve_order) ) );

        /// S[0] = S[0] * G3a^(xi^9 z^2)
        /// total_eval = total_eval + xi^9 z^2 g3(beta3)
        /// r = xi^9 z^2
        r = mulmod(r, verifier_challenges.xi, curve_order);
        S[0] = Pairing.addition(S[0], Pairing.scalar_mul(polys_to_verify.g3.commitment, r));
        total_eval = addmod(total_eval, mulmod(r,polys_to_verify.g3.evaluation, curve_order), curve_order);

        /// S[0] = S[0] * G3b^(xi^10 z^2) * (g^(x^(d-b2)))^(- xi^10 z^2 g3(beta3))
        /// total_eval = total_eval + xi^10 z^2 g3(beta3)
        /// r = xi^10 z^2
        r = mulmod(r, verifier_challenges.xi, curve_order);
        S[0] = Pairing.addition(S[0], Pairing.scalar_mul(polys_to_verify.g3_bound.commitment, r));
        S[0] = Pairing.addition(S[0], Pairing.scalar_mul(srs_g_bounds2,
                curve_order - mulmod(r, polys_to_verify.g3_bound.evaluation, curve_order) ) );

        /// S[0] = S[0] *  W2^(z^2 * beta3)
        /// S[1] = W0 * W1^z * W2^(z^2)
        S[0] = Pairing.addition(S[0], Pairing.scalar_mul(Pairing.G1Point(proof[36], proof[37]),
                mulmod( verifier_challenges.beta3, mulmod( verifier_challenges.z, verifier_challenges.z, curve_order ), curve_order ) ) );
        S[1] = Pairing.addition(S[1], Pairing.scalar_mul( Pairing.G1Point(proof[36], proof[37]),
                mulmod( verifier_challenges.z, verifier_challenges.z, curve_order ) ) );

        /// S[0] = S[0] * g^(-total_eval)
        S[0] = Pairing.addition(S[0], Pairing.scalar_mul(Pairing.G1Point(1,2), curve_order - total_eval));


        bool b = Pairing.pairingProd2(S[0], srs_h1, Pairing.negate(S[1]), srs_hx );

        return b;
    }


    struct polys_to_verify_struct {
        polys_to_verify_entry_struct zA;
        polys_to_verify_entry_struct lincheck1;
        polys_to_verify_entry_struct lincheck2;
        polys_to_verify_entry_struct lincheck3;
        polys_to_verify_entry_struct rc_A;
        polys_to_verify_entry_struct rc_B;
        polys_to_verify_entry_struct rc_C;
        polys_to_verify_entry_struct g1_and_2;
        polys_to_verify_entry_struct g1_and_2_bound;
        polys_to_verify_entry_struct g3;
        polys_to_verify_entry_struct g3_bound;
    }

    struct verifier_challenges_struct {
        uint alpha;
        uint eta_A;
        uint eta_B;
        uint eta_C;
        uint beta1;
        uint beta2;
        uint beta3;
        uint z;
        uint xi;
    }

    struct polys_to_verify_entry_struct {
        Pairing.G1Point commitment;
        uint256 evaluation;
    }

    /// finding linear combinations of the proof elements that should evaluate to certain values.

    function set_polys_to_verify(uint[<%instance_size%>] memory instance, uint[38] memory proof,
    verifier_challenges_struct memory verifier_challenges) internal view returns(
        polys_to_verify_struct memory polys_to_verify
        ) {

        /// zA(X) -- > zA(beta1)
        polys_to_verify.zA.commitment = Pairing.G1Point(proof[10], proof[11]);
        polys_to_verify.zA.evaluation = proof[7] ;

        /// c1(X) = h1(X)v_H(beta1) + g1(X)beta1
        ///         - r(alpha,beta1)(eta_A zA(X) + eta_B zB(X) + eta_C zA(beta1) zB(X))
        ///         + w_hat(X) v_(Hinstance)(beta1) + instance(beta1) -- > c1(beta1) = 0
        polys_to_verify = set_lincheck1_commitment(instance, proof, verifier_challenges, polys_to_verify);
        polys_to_verify.lincheck1.evaluation = 0;

        /// c2(X) = h2(X)vH(beta2) + beta2 g2(X) + (sigma2 / |H| - sigma3 r(alpha,beta2))

        /// c2(X) = h2(X)vH(beta2)
        polys_to_verify.lincheck2.commitment = Pairing.scalar_mul(
            Pairing.G1Point(proof[20], proof[21]),
            (exponeniate_by_power_of_2(verifier_challenges.beta2, log_domain_size_H) - 1)
            );

        /// c2(X) = c2(X) + beta2 g2(X)
        polys_to_verify.lincheck2.commitment = Pairing.addition(
            polys_to_verify.lincheck2.commitment,
            Pairing.scalar_mul(
                Pairing.G1Point(proof[22], proof[23]),
                verifier_challenges.beta2
                )
            );

        /// c2(X) = c2(X) +  (sigma2 / |H| - sigma3 r(alpha,beta2))
        polys_to_verify.lincheck2.commitment = Pairing.addition(
            polys_to_verify.lincheck2.commitment,
            Pairing.scalar_mul(
                Pairing.G1Point(1,2),
                submod(mulmod(proof[0], inverse_domain_size_H,curve_order),
                    mulmod(proof[1], vanishing_poly_eval(verifier_challenges.alpha, verifier_challenges.beta2), curve_order)
                    )
                )
            );

        /// ---> c2(beta2) = 0
        polys_to_verify.lincheck3.evaluation = 0;

        /// c3(X) = h3(X)vK(beta3) - sum_i eta_i vH(beta1)vH(beta2) val_i(X) prod_(j != i) rc_evals[j] + (beta3 g3(beta3) + sigma3 / |K|) prod_i rc_evals
        polys_to_verify = set_lincheck3_commitment(proof, verifier_challenges, polys_to_verify);

        /// rcA(X) = (rowA(X) - beta2)(colA(X) - beta1)
        /// rcB(X) = (rowB(X) - beta2)(colB(X) - beta1)
        /// rcA(X) = (rowC(X) - beta2)(colC(X) - beta1)

        /// rcA(X) = beta1 * beta2
        polys_to_verify.rc_A.commitment = Pairing.scalar_mul(
            Pairing.G1Point(1,2),
            mulmod(verifier_challenges.beta1,verifier_challenges.beta2,curve_order)
            );

        /// rcB(X) = beta1 * beta2, rcC(X) = beta1 * beta2
        polys_to_verify.rc_B.commitment = polys_to_verify.rc_A.commitment;
        polys_to_verify.rc_C.commitment = polys_to_verify.rc_A.commitment;

        /// rcA(X) = rcA(X) - beta1 rowA(X)
        polys_to_verify.rc_A.commitment = Pairing.addition(
            polys_to_verify.rc_A.commitment,
            Pairing.scalar_mul( row_com_A, curve_order - verifier_challenges.beta1)
            );

        /// rcB(X) = rcB(X) - beta1 rowB(X)
        polys_to_verify.rc_B.commitment = Pairing.addition(
            polys_to_verify.rc_B.commitment,
            Pairing.scalar_mul( row_com_B, curve_order - verifier_challenges.beta1)
            );

        /// rcC(X) = rcC(X) - beta1 rowC(X)
        polys_to_verify.rc_C.commitment = Pairing.addition(
            polys_to_verify.rc_C.commitment,
            Pairing.scalar_mul(row_com_C, curve_order - verifier_challenges.beta1)
            );

        /// rcA(X) = rcA(X) - beta2 colA(X)
        polys_to_verify.rc_A.commitment = Pairing.addition(
            polys_to_verify.rc_A.commitment,
            Pairing.scalar_mul( col_com_A, curve_order - verifier_challenges.beta2)
            );

        /// rcB(X) = rcB(X) - beta2 colB(X)
        polys_to_verify.rc_B.commitment = Pairing.addition(
            polys_to_verify.rc_B.commitment,
            Pairing.scalar_mul( col_com_B, curve_order - verifier_challenges.beta2)
            );

        /// rcC(X) = rcC(X) - beta2 colC(X)
        polys_to_verify.rc_C.commitment = Pairing.addition(
            polys_to_verify.rc_C.commitment,
            Pairing.scalar_mul(col_com_C, curve_order - verifier_challenges.beta2)
            );

        /// rcA(X) = rcA(X) + rowA(X) * colA(X)
        /// rcB(X) = rcB(X) + rowB(X) * colB(X)
        /// rcC(X) = rcC(X) + rowC(X) * colC(X)
        polys_to_verify.rc_A.commitment = Pairing.addition(polys_to_verify.rc_A.commitment, row_times_col_com_A);
        polys_to_verify.rc_B.commitment = Pairing.addition(polys_to_verify.rc_B.commitment, row_times_col_com_B);
        polys_to_verify.rc_C.commitment = Pairing.addition(polys_to_verify.rc_C.commitment, row_times_col_com_C);

        /// rcA(beta3), rcB(beta3), rcC(beta3)
        polys_to_verify.rc_A.evaluation = proof[3];
        polys_to_verify.rc_B.evaluation = proof[4];
        polys_to_verify.rc_C.evaluation = proof[5];

        /// c4(X) = g1(X) + beta2 g2(X) --> c4(beta3)
        polys_to_verify.g1_and_2.commitment = Pairing.addition(
            Pairing.G1Point(proof[16], proof[17]),
            Pairing.scalar_mul(
                Pairing.G1Point(proof[22], proof[23]),
                verifier_challenges.beta2
                )
            );
        polys_to_verify.g1_and_2.evaluation = proof[6];

        /// c4(X) X^(d - b1) --> c4(beta3)
        polys_to_verify.g1_and_2_bound.commitment = Pairing.addition(
            Pairing.G1Point(proof[18], proof[19]),
            Pairing.scalar_mul(
                Pairing.G1Point(proof[24], proof[25]),
                verifier_challenges.beta2
                )
            );
        polys_to_verify.g1_and_2_bound.evaluation = proof[6];

        /// g3(X) --> g3(beta3)
        polys_to_verify.g3.commitment = Pairing.G1Point( proof[28], proof[29] );
        polys_to_verify.g3.evaluation = proof[2];

        /// g3(X) X^(d - b2) --> g3(beta3)
        polys_to_verify.g3_bound.commitment = Pairing.G1Point( proof[30], proof[31] );
        polys_to_verify.g3_bound.evaluation = proof[2];

        }

    /// r(a,b) = (a^n - b^n) / (a - b)
    function vanishing_poly_eval(uint256 a, uint256 b) internal pure returns (uint256) {
        uint256 r = exponeniate_by_power_of_2(b,log_domain_size_H);
         r = submod( exponeniate_by_power_of_2(a,log_domain_size_H), r );
         r = mulmod( ECCMath.invmod( submod(a, b ), curve_order ) , r , curve_order);
         return r;
    }

    /// c1(X) = h1(X)v_H(beta1) + g1(X)beta1
    ///         - r(alpha,beta1)(eta_A zA(X) + eta_B zB(X) + eta_C zA(beta1) zB(X))
    ///         + w_hat(X) v_(Hinstance)(beta1) + instance(beta1) -- > c1(beta1) = 0

    function set_lincheck1_commitment(uint[<%instance_size%>] memory instance,
    uint[38] memory proof,
    verifier_challenges_struct memory verifier_challenges,
    polys_to_verify_struct memory polys_to_verify) internal view
    returns(polys_to_verify_struct memory) {

        instance_lagrange_basis_struct memory instance_lagrange_basis = set_instance_lagrange_basis();

        /// r = beta1^n
        uint256 r = exponeniate_by_power_of_2(verifier_challenges.beta1,log_domain_size_H);

        /// c1(X) = h1(X)(beta1^n - 1) = h1(X) v_H(beta1)
        polys_to_verify.lincheck1.commitment = Pairing.scalar_mul( Pairing.G1Point( proof[14], proof[15]), r - 1 ) ;

        /// c1(X) = c1(X) + g1(X) beta1
        polys_to_verify.lincheck1.commitment = Pairing.addition( polys_to_verify.lincheck1.commitment,
        Pairing.scalar_mul( Pairing.G1Point(proof[16], proof[17]) , verifier_challenges.beta1 ) );

        /// - r(alpha,beta1) = - (alpha^n - beta1^n) / (alpha - beta1)
        r = vanishing_poly_eval(verifier_challenges.alpha, verifier_challenges.beta1);
        r = (curve_order -  r ) % curve_order;

        /// c1(X) = c1(X) - r(alpha,beta1) eta_A zA(X)
        polys_to_verify.lincheck1.commitment = Pairing.addition( polys_to_verify.lincheck1.commitment,
        Pairing.scalar_mul( Pairing.G1Point(proof[10], proof[11]) , mulmod(r , verifier_challenges.eta_A, curve_order ) ) );

        /// c1(X) = c1(X) - r(alpha,beta1) (eta_B + etaC zAbeta1) zB(X)
        polys_to_verify.lincheck1.commitment = Pairing.addition( polys_to_verify.lincheck1.commitment,
        Pairing.scalar_mul( Pairing.G1Point(proof[12], proof[13]) ,
            mulmod(r ,
            addmod(verifier_challenges.eta_B, mulmod( verifier_challenges.eta_C , proof[7], curve_order), curve_order),
            curve_order) )
        );

        /// r = (beta1 - 1) (beta1 - eta_1) (beta2 - eta_2) = v_(Hinstance)(beta1)
        r = mulmod(proof[0] , (verifier_challenges.beta1 - 1), curve_order);
        r = mulmod(r, submod(verifier_challenges.beta1, 19540430494807482326159819597004422086093766032135589407132600596362845576832), curve_order);
        r = mulmod(r, submod(verifier_challenges.beta1, 21888242871839275217838484774961031246007050428528088939761107053157389710902), curve_order);

        /// c1(X) = c1(X) + v_(Hinstance)(beta1) w_hat(X)
        polys_to_verify.lincheck1.commitment = Pairing.addition( polys_to_verify.lincheck1.commitment,
        Pairing.scalar_mul( Pairing.G1Point(proof[8], proof[9]) , r ) );

        <%r_lincheck1_loop%>

        /// r = r * sigma2
        r = mulmod( r , proof[0], curve_order );

        /// c1(X) = c1(X) + sigma2 * instance(beta1)
        polys_to_verify.lincheck1.commitment = Pairing.addition( polys_to_verify.lincheck1.commitment,
        Pairing.scalar_mul( Pairing.G1Point(1, 2) , r ) );

        return polys_to_verify;
    }

    /// c3(X) = h3(X)vK(beta3) - sum_i eta_i vH(beta1)vH(beta2) val_i(X) prod_(j != i) rc_evals[j] + (beta3 g3(beta3) + sigma3 / |K|) prod_i rc_evals

    function set_lincheck3_commitment(
        uint[38] memory proof,
        verifier_challenges_struct memory verifier_challenges,
        polys_to_verify_struct memory polys_to_verify) internal view
        returns(polys_to_verify_struct memory) {

            /// c3(X) = h3(X)vK(beta3)
            polys_to_verify.lincheck3.commitment = Pairing.scalar_mul(
                Pairing.G1Point(proof[26], proof[27]),
                exponeniate_by_power_of_2(verifier_challenges.beta3, log_domain_size_K) - 1
                );

            /// r = (beta3 g3(beta3) + sigma3 / |K| )
            uint256 r = mulmod( mulmod(proof[3],proof[4], curve_order), proof[5], curve_order);
            r = mulmod( r,
                addmod(
                    mulmod( verifier_challenges.beta3, proof[2], curve_order),
                    mulmod( proof[1], inverse_domain_size_K, curve_order),
                    curve_order
                    ),
                curve_order );

            /// c3(X) = c3(X) + (beta3 g3(beta3) + sigma3 / |K|
            polys_to_verify.lincheck3.commitment = Pairing.addition(
                polys_to_verify.lincheck3.commitment,
                Pairing.scalar_mul(
                    Pairing.G1Point( 1, 2),
                    r
                    )
                );

            /// - r = -  vH(beta1)vH(beta2) = - (beta1^n - 1) (beta2^n - 1)
            r = curve_order - mulmod(
                exponeniate_by_power_of_2(verifier_challenges.beta1, log_domain_size_K) - 1,
                exponeniate_by_power_of_2(verifier_challenges.beta2, log_domain_size_K) - 1,
                curve_order
                );

            /// c3(X) = c3(X) -  vH(beta1)vH(beta2) eta_A rcB(beta3) rcC(beta3) val_A(X)
            polys_to_verify.lincheck3.commitment = Pairing.addition(
                polys_to_verify.lincheck3.commitment,
                Pairing.scalar_mul(
                    val_com_A,
                    mulmod(
                        r,
                        mulmod(
                            verifier_challenges.eta_A,
                            mulmod(proof[4], proof[5], curve_order),
                            curve_order
                                ),
                        curve_order
                        )
                    )
                );

            /// c3(X) = c3(X) -  vH(beta1)vH(beta2) eta_B rcA(beta3) rcC(beta3) val_B(X)
            polys_to_verify.lincheck3.commitment = Pairing.addition(
                polys_to_verify.lincheck3.commitment,
                Pairing.scalar_mul(
                    val_com_B,
                    mulmod(
                        r,
                        mulmod(
                            verifier_challenges.eta_B,
                            mulmod(proof[3], proof[5], curve_order),
                            curve_order
                                ),
                        curve_order
                        )
                    )
                );

            /// c3(X) = c3(X) -  vH(beta1)vH(beta2) eta_C rcA(beta3) rcB(beta3) val_C(X)
            polys_to_verify.lincheck3.commitment = Pairing.addition(
                polys_to_verify.lincheck3.commitment,
                Pairing.scalar_mul(
                    val_com_C,
                    mulmod(
                        r,
                        mulmod(
                            verifier_challenges.eta_C,
                            mulmod(proof[3], proof[4], curve_order),
                            curve_order
                                ),
                        curve_order
                        )
                    )
                );

            return polys_to_verify;
        }

    /// Fiat-Shamir proof elements to find verifier challenges
    function get_verifier_challenges(
        uint256[<%instance_size%>] memory instance,
        uint256[38] memory proof
    ) internal pure returns(verifier_challenges_struct memory verifier_challenges) {

        /// hash the instance and the srs
        uint256 current_hash = hash_integers(<%instance_padded%>, <%instance_size%>);
        current_hash = hash_integers([current_hash, srs_hash,0,0,0,0,0,0],2);

        /// hash the first round w_hat(X), zA(X), zB(X) to get alpha
        uint256[8] memory values = [current_hash, proof[8], proof[9], proof[10], proof[11], proof[12], proof[13], 0];
        current_hash = hash_integers(values, 7);
        verifier_challenges.alpha = current_hash % curve_order;

        /// hash again to get eta_A
        values = [current_hash, 0, 0, 0, 0, 0, 0, 0];
        current_hash = hash_integers(values, 1);
        verifier_challenges.eta_A = current_hash % curve_order;

        /// hash again to get eta_B
        values = [current_hash, 0, 0, 0, 0, 0, 0, 0];
        current_hash = hash_integers(values, 1);
        verifier_challenges.eta_B = current_hash % curve_order;

        /// hash again to get eta_C
        values = [current_hash, 0, 0, 0, 0, 0, 0, 0];
        current_hash = hash_integers(values, 1);
        verifier_challenges.eta_C = current_hash % curve_order;

        /// hash the second round h1(X), g1a(X), g1b(X) to get beta1
        values = [current_hash, proof[14], proof[15], proof[16], proof[17], proof[18], proof[19], 0];
        current_hash = hash_integers(values, 7);
        verifier_challenges.beta1 = current_hash % curve_order ;

        /// hash the third round sigma2, h2(X), g2a(X), g2b(X) to get beta2
        values = [current_hash, proof[0], proof[20], proof[21], proof[22], proof[23], proof[24], proof[25] ];
        current_hash = hash_integers(values, 8);
        verifier_challenges.beta2 = current_hash % curve_order;

        /// hash the fourth round sigma3, h3(X), g3a(X), g3b(X) to get beta2
        values = [current_hash, proof[1], proof[26], proof[27], proof[28], proof[29], proof[30], proof[31] ];
        current_hash = hash_integers(values, 8);
        verifier_challenges.beta3 = current_hash % curve_order;

        /// hash the fifth round g3(beta3), rcA(beta3), rcB(beta3), rcC(beta3), c4(beta3), zA(beta1) to get xi
        values = [current_hash, proof[2], proof[3], proof[4], proof[5], proof[6], proof[7], 0];
        current_hash = hash_integers(values, 7);
        verifier_challenges.xi = current_hash % curve_order;

        /// hash the sixth round W0, W1, W2 to get z
        values = [current_hash, proof[32], proof[33], proof[34], proof[35], proof[36], proof[37], 0];
        current_hash = hash_integers(values, 7);
        verifier_challenges.z = current_hash % curve_order;

    }

    /// Function for hashing a list of integers of length num_of_values.
    /// Pass in a list of length 8 (pad with zeros if necessary)
    /// For each value in the list up to num_of_vals, append them with the output from the previous hash, and then sha256 the 512 bit input
    /// Returns a 256 bit integer
    function hash_integers(uint256[8] memory values,uint256 num_of_values) internal pure returns(uint) {
        bytes32 k = "" ;

        for (uint i = 0; i < num_of_values; i++) {
            k = sha256(abi.encode(k,bytes32(values[i])));
        }

        return( uint256(k) );
    }
}
"#;
