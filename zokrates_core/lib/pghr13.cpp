/**
 * @file pghr13.cpp
 * @author Jacob Eberhardt <jacob.eberhardt@tu-berlin.de
 * @author Dennis Kuhnert <dennis.kuhnert@campus.tu-berlin.de>
 * @date 2017
 */

#include "pghr13.hpp"

#include <cassert>
#include <sstream>
#include <string>

// contains definition of alt_bn128 ec public parameters
#include "libff/algebra/curves/alt_bn128/alt_bn128_pp.hpp"
// contains required interfaces and types (keypair, proof, generator, prover, verifier)
#include <libsnark/zk_proof_systems/ppzksnark/r1cs_ppzksnark/r1cs_ppzksnark.hpp>

using namespace libsnark;

#include "util.tcc"

namespace pghr13 {

template <mp_size_t Q, typename ppT, typename G1, typename G2>
std::string serializeVerificationKey(r1cs_ppzksnark_verification_key<ppT>* vk)
{
    std::stringstream ss;
    unsigned icLength = vk->encoded_IC_query.rest.indices.size();

    ss << "{";
    ss << "\"a\":" << outputPointG2AffineAsHexJson<Q, G2>(vk->alphaA_g2) << ",";
    ss << "\"b\":" << outputPointG1AffineAsHexJson<Q, G1>(vk->alphaB_g1) << ",";
    ss << "\"c\":" << outputPointG2AffineAsHexJson<Q, G2>(vk->alphaC_g2) << ",";
    ss << "\"gamma\":" << outputPointG2AffineAsHexJson<Q, G2>(vk->gamma_g2) << ",";
    ss << "\"gamma_beta_1\":" << outputPointG1AffineAsHexJson<Q, G1>(vk->gamma_beta_g1) << ",";
    ss << "\"gamma_beta_2\":" << outputPointG2AffineAsHexJson<Q, G2>(vk->gamma_beta_g2) << ",";
    ss << "\"z\":" << outputPointG2AffineAsHexJson<Q, G2>(vk->rC_Z_g2) << ",";
    ss << "\"ic\":[";
    ss << outputPointG1AffineAsHexJson<Q, G1>(vk->encoded_IC_query.first);
    for (size_t i = 0; i < icLength; ++i) {
        ss << ",";
        ss << outputPointG1AffineAsHexJson<Q, G1>(vk->encoded_IC_query.rest.values[i]);
    }
    ss << "],";
    ss << "\"raw\":\"" << encodeToHexString<2>(serialize(*vk)) << "\"";
    ss << "}";
    std::string str = ss.str();
    return str;
}

template <mp_size_t Q, mp_size_t R, typename ppT, typename G1, typename G2>
std::string serializeProof(r1cs_ppzksnark_proof<ppT>* proof, const uint8_t* public_inputs, int public_inputs_length)
{
    std::stringstream ss;
    ss << "{";
    ss << "\"proof\":{";
    ss << "\"a\":" << outputPointG1AffineAsHexJson<Q, G1>(proof->g_A.g) << ",";
    ss << "\"a_p\":" << outputPointG1AffineAsHexJson<Q, G1>(proof->g_A.h) << ",";
    ss << "\"b\":" << outputPointG2AffineAsHexJson<Q, G2>(proof->g_B.g) << ",";
    ss << "\"b_p\":" << outputPointG1AffineAsHexJson<Q, G1>(proof->g_B.h) << ",";
    ss << "\"c\":" << outputPointG1AffineAsHexJson<Q, G1>(proof->g_C.g) << ",";
    ss << "\"c_p\":" << outputPointG1AffineAsHexJson<Q, G1>(proof->g_C.h) << ",";
    ss << "\"h\":" << outputPointG1AffineAsHexJson<Q, G1>(proof->g_H) << ",";
    ss << "\"k\":" << outputPointG1AffineAsHexJson<Q, G1>(proof->g_K);
    ss << "},";
    ss << "\"inputs\":[";
    for (int i = 1; i < public_inputs_length; i++) {
        if (i != 1) {
            ss << ",";
        }
        ss << outputInputAsHex<R>(libsnarkBigintFromBytes<R>(public_inputs + (i * R * sizeof(mp_limb_t))));
    }
    ss << "],";
    ss << "\"raw\":\"" << encodeToHexString<2>(serialize(*proof)) << "\"";
    ss << "}";
    std::string str = ss.str();
    return str;
}

template <mp_size_t Q, mp_size_t R, typename ppT, typename G1, typename G2>
setup_result_t setup(const uint8_t* a, const uint8_t* b, const uint8_t* c, int32_t a_len, int32_t b_len, int32_t c_len, int32_t constraints, int32_t variables, int32_t inputs)
{
    libff::inhibit_profiling_info = true;
    libff::inhibit_profiling_counters = true;

    // initialize curve parameters
    ppT::init_public_params();

    auto cs = createConstraintSystem<r1cs_ppzksnark_constraint_system, R, ppT>(a, b, c, a_len, b_len, c_len, constraints, variables, inputs);
    assert(cs.num_variables() >= (unsigned)inputs);
    assert(cs.num_inputs() == (unsigned)inputs);
    assert(cs.num_constraints() == (unsigned)constraints);

    r1cs_ppzksnark_keypair<ppT> keypair = r1cs_ppzksnark_generator<ppT>(cs);
    auto vk = serializeVerificationKey<Q, ppT, G1, G2>(&keypair.vk);

    buffer_t vk_buf = createBuffer(vk);
    buffer_t pk_buf = createBuffer(keypair.pk);

    setup_result_t result(vk_buf, pk_buf);
    return result;
}

template <mp_size_t Q, mp_size_t R, typename ppT, typename G1, typename G2>
proof_result_t generateProof(buffer_t* pk_buf, const uint8_t* public_inputs, int32_t public_inputs_length, const uint8_t* private_inputs, int32_t private_inputs_length)
{
    libff::inhibit_profiling_info = true;
    libff::inhibit_profiling_counters = true;

    // initialize curve parameters
    ppT::init_public_params();

    r1cs_ppzksnark_proving_key<ppT> proving_key;
    fromBuffer<r1cs_ppzksnark_proving_key<ppT>>(pk_buf, proving_key);

    // assign variables based on witness values, excludes ~one
    r1cs_variable_assignment<libff::Fr<ppT>> full_variable_assignment;
    for (int i = 1; i < public_inputs_length; i++) {
        full_variable_assignment.push_back(libff::Fr<ppT>(libsnarkBigintFromBytes<R>(public_inputs + (i * R * sizeof(mp_limb_t)))));
    }
    for (int i = 0; i < private_inputs_length; i++) {
        full_variable_assignment.push_back(libff::Fr<ppT>(libsnarkBigintFromBytes<R>(private_inputs + (i * R * sizeof(mp_limb_t)))));
    }

    r1cs_primary_input<libff::Fr<ppT>> primary_input(
        full_variable_assignment.begin(),
        full_variable_assignment.begin() + public_inputs_length - 1);

    r1cs_primary_input<libff::Fr<ppT>> auxiliary_input(
        full_variable_assignment.begin() + public_inputs_length - 1,
        full_variable_assignment.end());

    r1cs_ppzksnark_proof<ppT> proof = r1cs_ppzksnark_prover<ppT>(proving_key, primary_input, auxiliary_input);
    std::string json = serializeProof<Q, R, ppT, G1, G2>(&proof, public_inputs, public_inputs_length);

    buffer_t proof_buf = createBuffer(json);
    proof_result_t result(proof_buf);
    return result;
}

template <mp_size_t R, typename ppT>
bool verify(buffer_t* vk_buf, buffer_t* proof_buf, const uint8_t* public_inputs, int32_t public_inputs_length)
{
    libff::inhibit_profiling_info = true;
    libff::inhibit_profiling_counters = true;

    // initialize curve parameters
    ppT::init_public_params();

    r1cs_ppzksnark_verification_key<ppT> vk;
    r1cs_ppzksnark_proof<ppT> proof;

    fromBuffer<r1cs_ppzksnark_verification_key<ppT>>(vk_buf, vk);
    fromBuffer<r1cs_ppzksnark_proof<ppT>>(proof_buf, proof);

    r1cs_primary_input<libff::Fr<ppT>> primary_input;
    for (int i = 0; i < public_inputs_length; i++) {
        primary_input.push_back(libff::Fr<ppT>(libsnarkBigintFromBytes<R>(public_inputs + (i * R * sizeof(mp_limb_t)))));
    }
    return r1cs_ppzksnark_verifier_strong_IC<ppT>(vk, primary_input, proof);
}
}

setup_result_t pghr13_bn128_setup(const uint8_t* a, const uint8_t* b, const uint8_t* c, int32_t a_len, int32_t b_len, int32_t c_len, int32_t constraints, int32_t variables, int32_t inputs)
{
    return pghr13::setup<libff::alt_bn128_q_limbs,
        libff::alt_bn128_r_limbs,
        libff::alt_bn128_pp,
        libff::alt_bn128_G1,
        libff::alt_bn128_G2>(a, b, c, a_len, b_len, c_len, constraints, variables, inputs);
}

proof_result_t pghr13_bn128_generate_proof(buffer_t* pk_buf,
    const uint8_t* public_inputs,
    int32_t public_inputs_length,
    const uint8_t* private_inputs,
    int32_t private_inputs_length)
{
    return pghr13::generateProof<libff::alt_bn128_q_limbs,
        libff::alt_bn128_r_limbs,
        libff::alt_bn128_pp,
        libff::alt_bn128_G1,
        libff::alt_bn128_G2>(pk_buf,
        public_inputs,
        public_inputs_length,
        private_inputs,
        private_inputs_length);
}

bool pghr13_bn128_verify(buffer_t* vk_buf, buffer_t* proof_buf, const uint8_t* public_inputs, int32_t public_inputs_length)
{
    return pghr13::verify<libff::alt_bn128_r_limbs,
        libff::alt_bn128_pp>(vk_buf, proof_buf, public_inputs, public_inputs_length);
}