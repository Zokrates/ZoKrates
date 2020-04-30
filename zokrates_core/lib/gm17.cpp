/**
 * @file gm17.cpp
 * @author Jacob Eberhardt <jacob.eberhardt@tu-berlin.de
 * @author Dennis Kuhnert <dennis.kuhnert@campus.tu-berlin.de>
 * @date 2017
 */

#include "gm17.hpp"
#include "util.hpp"
#include <cassert>
#include <sstream>
#include <string>

// contains definition of alt_bn128 ec public parameters
#include "libff/algebra/curves/alt_bn128/alt_bn128_pp.hpp"

// contains required interfaces and types (keypair, proof, generator, prover, verifier)
#include <libsnark/zk_proof_systems/ppzksnark/r1cs_se_ppzksnark/r1cs_se_ppzksnark.hpp>

typedef long integer_coeff_t;

using namespace libsnark;
using std::cout;
using std::endl;

namespace gm17 {
r1cs_se_ppzksnark_constraint_system<libff::alt_bn128_pp> createConstraintSystem(const uint8_t* a, const uint8_t* b, const uint8_t* c, int32_t a_len, int32_t b_len, int32_t c_len, int32_t constraints, int32_t variables, int32_t inputs)
{
    r1cs_se_ppzksnark_constraint_system<libff::alt_bn128_pp> cs;
    cs.primary_input_size = inputs;
    cs.auxiliary_input_size = variables - inputs - 1; // ~one not included

    cout << "num variables: " << variables << endl;
    cout << "num constraints: " << constraints << endl;
    cout << "num inputs: " << inputs << endl;

    struct VariableValueMapping {
        int constraint_id;
        int variable_id;
        uint8_t variable_value[32];
    };

    const VariableValueMapping* a_vvmap = (VariableValueMapping*)a;
    const VariableValueMapping* b_vvmap = (VariableValueMapping*)b;
    const VariableValueMapping* c_vvmap = (VariableValueMapping*)c;

    int a_id = 0;
    int b_id = 0;
    int c_id = 0;

    // initialize curve parameters
    libff::alt_bn128_pp::init_public_params();

    for (int row = 0; row < constraints; row++) {
        linear_combination<libff::Fr<libff::alt_bn128_pp>> lin_comb_a, lin_comb_b, lin_comb_c;
        while (a_id < a_len && a_vvmap[a_id].constraint_id == row) {
            libff::bigint<libff::alt_bn128_r_limbs> value = libsnarkBigintFromBytes(a_vvmap[a_id].variable_value);
            if (!value.is_zero()) {
                lin_comb_a.add_term(a_vvmap[a_id].variable_id, value);
            }
            a_id++;
        }
        while (b_id < b_len && b_vvmap[b_id].constraint_id == row) {
            libff::bigint<libff::alt_bn128_r_limbs> value = libsnarkBigintFromBytes(b_vvmap[b_id].variable_value);
            if (!value.is_zero()) {
                lin_comb_b.add_term(b_vvmap[b_id].variable_id, value);
            }
            b_id++;
        }
        while (c_id < c_len && c_vvmap[c_id].constraint_id == row) {
            libff::bigint<libff::alt_bn128_r_limbs> value = libsnarkBigintFromBytes(c_vvmap[c_id].variable_value);
            if (!value.is_zero()) {
                lin_comb_c.add_term(c_vvmap[c_id].variable_id, value);
            }
            c_id++;
        }
        cs.add_constraint(r1cs_constraint<libff::Fr<libff::alt_bn128_pp>>(lin_comb_a, lin_comb_b, lin_comb_c));
    }
    return cs;
}

r1cs_se_ppzksnark_keypair<libff::alt_bn128_pp> generateKeypair(const r1cs_se_ppzksnark_constraint_system<libff::alt_bn128_pp>& cs)
{
    return r1cs_se_ppzksnark_generator<libff::alt_bn128_pp>(cs); //from r1cs_se_ppzksnark.hpp
}

std::string serializeVerificationKey(r1cs_se_ppzksnark_verification_key<libff::alt_bn128_pp>* vk)
{
    std::stringstream ss;
    unsigned queryLength = vk->query.size();
    ss << "{";
    ss << "\"h\":" << outputPointG2AffineAsHexJson(vk->H) << ",";
    ss << "\"g_alpha\":" << outputPointG1AffineAsHexJson(vk->G_alpha) << ",";
    ss << "\"h_beta\":" << outputPointG2AffineAsHexJson(vk->H_beta) << ",";
    ss << "\"g_gamma\":" << outputPointG1AffineAsHexJson(vk->G_gamma) << ",";
    ss << "\"h_gamma\":" << outputPointG2AffineAsHexJson(vk->H_gamma) << ",";
    ss << "\"query\":[";
    for (size_t i = 0; i < queryLength; ++i) {
        if (i != 0) ss << ",";
        ss << outputPointG1AffineAsHexJson(vk->query[i]);
    }
    ss << "],";
    ss << "\"raw\":\"" << toHexString(serialize(*vk)) << "\"";
    ss << "}";
    std::string str = ss.str();
    return str;
}

std::string serializeProof(r1cs_se_ppzksnark_proof<libff::alt_bn128_pp>* proof, const uint8_t* public_inputs, int32_t public_inputs_length)
{
    std::stringstream ss;
    ss << "{";
    ss << "\"points\":{";
    ss << "\"a\":" << outputPointG1AffineAsHexJson(proof->A) << ",";
    ss << "\"b\":" << outputPointG2AffineAsHexJson(proof->B) << ",";
    ss << "\"c\":" << outputPointG1AffineAsHexJson(proof->C);
    ss << "},";
    ss << "\"inputs\":[";
    for (int i = 1; i < public_inputs_length; i++) {
        if (i != 1) {
            ss << ",";
        }
        ss << outputInputAsHex(libsnarkBigintFromBytes(public_inputs + i * 32));
    }
    ss << "],";
    ss << "\"raw\":\"" << toHexString(serialize(*proof)) << "\"";
    ss << "}";
    std::string str = ss.str();
    return str;
}
}

setup_result_t gm17_setup(const uint8_t* A, const uint8_t* B, const uint8_t* C, int32_t a_len, int32_t b_len, int32_t c_len, int32_t constraints, int32_t variables, int32_t inputs)
{
    libff::inhibit_profiling_info = true;
    libff::inhibit_profiling_counters = true;

    // initialize curve parameters
    libff::alt_bn128_pp::init_public_params();

    auto cs = gm17::createConstraintSystem(A, B, C, a_len, b_len, c_len, constraints, variables, inputs);
    assert(cs.num_variables() >= (unsigned)inputs);
    assert(cs.num_inputs() == (unsigned)inputs);
    assert(cs.num_constraints() == (unsigned)constraints);

    // create keypair
    auto keypair = r1cs_se_ppzksnark_generator<libff::alt_bn128_pp>(cs);
    auto vk = gm17::serializeVerificationKey(&keypair.vk);

    buffer_t vk_buf = create_buffer(vk);
    buffer_t pk_buf = create_buffer(keypair.pk);

    setup_result_t result(vk_buf, pk_buf);
    return result;
}

proof_result_t gm17_generate_proof(buffer_t* pk_buf, const uint8_t* public_inputs, int32_t public_inputs_length, const uint8_t* private_inputs, int32_t private_inputs_length)
{
    libff::inhibit_profiling_info = true;
    libff::inhibit_profiling_counters = true;

    //initialize curve parameters
    libff::alt_bn128_pp::init_public_params();

    r1cs_se_ppzksnark_proving_key<libff::alt_bn128_pp> proving_key;
    from_buffer<r1cs_se_ppzksnark_proving_key<libff::alt_bn128_pp>>(pk_buf, proving_key);

    // assign variables based on witness values, excludes ~one
    r1cs_variable_assignment<libff::Fr<libff::alt_bn128_pp>> full_variable_assignment;
    for (int i = 1; i < public_inputs_length; i++) {
        full_variable_assignment.push_back(libff::Fr<libff::alt_bn128_pp>(libsnarkBigintFromBytes(public_inputs + i * 32)));
    }
    for (int i = 0; i < private_inputs_length; i++) {
        full_variable_assignment.push_back(libff::Fr<libff::alt_bn128_pp>(libsnarkBigintFromBytes(private_inputs + i * 32)));
    }

    // split up variables into primary and auxiliary inputs. Does *NOT* include the constant 1
    // Public variables belong to primary input, private variables are auxiliary input.
    r1cs_primary_input<libff::Fr<libff::alt_bn128_pp>> primary_input(full_variable_assignment.begin(), full_variable_assignment.begin() + public_inputs_length - 1);
    r1cs_primary_input<libff::Fr<libff::alt_bn128_pp>> auxiliary_input(full_variable_assignment.begin() + public_inputs_length - 1, full_variable_assignment.end());

    // for debugging
    // cout << "full variable assignment:" << endl << full_variable_assignment;
    // cout << "primary input:" << endl << primary_input;
    // cout << "auxiliary input:" << endl << auxiliary_input;

    // Proof Generation
    auto proof = r1cs_se_ppzksnark_prover<libff::alt_bn128_pp>(proving_key, primary_input, auxiliary_input);
    auto proof_json = gm17::serializeProof(&proof, public_inputs, public_inputs_length);

    buffer_t proof_buf = create_buffer(proof_json);
    proof_result_t result(proof_buf);
    return result;
}

bool gm17_verify(buffer_t* vk_buf, buffer_t* proof_buf, const uint8_t* public_inputs, int32_t public_inputs_length)
{
    libff::inhibit_profiling_info = true;
    libff::inhibit_profiling_counters = true;

    // initialize curve parameters
    libff::alt_bn128_pp::init_public_params();

    r1cs_se_ppzksnark_verification_key<libff::alt_bn128_pp> vk;
    r1cs_se_ppzksnark_proof<libff::alt_bn128_pp> proof;

    from_buffer<r1cs_se_ppzksnark_verification_key<libff::alt_bn128_pp>>(vk_buf, vk);
    from_buffer<r1cs_se_ppzksnark_proof<libff::alt_bn128_pp>>(proof_buf, proof);

    r1cs_primary_input<libff::Fr<libff::alt_bn128_pp>> primary_input;
    for (int i = 0; i < public_inputs_length; i++) {
        primary_input.push_back(libff::Fr<libff::alt_bn128_pp>(libsnarkBigintFromBytes(public_inputs + i * 32)));
    }

    return r1cs_se_ppzksnark_verifier_strong_IC<libff::alt_bn128_pp>(vk, primary_input, proof);
}