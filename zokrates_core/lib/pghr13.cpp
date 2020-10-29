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
#include <libsnark/common/data_structures/accumulation_vector.hpp>
#include <libsnark/knowledge_commitment/knowledge_commitment.hpp>
#include <libsnark/zk_proof_systems/ppzksnark/r1cs_ppzksnark/r1cs_ppzksnark.hpp>

using namespace libsnark;

#include "util.tcc"

namespace pghr13 {

template <mp_size_t Q, typename ppT, typename G1, typename G2>
buffer_t serialize_verification_key(r1cs_ppzksnark_verification_key<ppT>* vk)
{
    const size_t QUERY_COUNT = vk->encoded_IC_query.rest.indices.size();

    const size_t G1_SIZE = Q * sizeof(mp_limb_t) * 2; // [x, y]
    const size_t G2_SIZE = Q * sizeof(mp_limb_t) * 4; // [[x0, x1], [y0, y1]]

    const size_t LENGTH = (G1_SIZE * 3) + (G2_SIZE * 5) + (QUERY_COUNT * G1_SIZE);

    // [ -------------------- LENGTH --------------------- ]
    // [ a, b, c, gamma, gamma_beta_1, gamma_beta_2, z, ic ]

    buffer_t buffer;
    buffer.data = (uint8_t*)malloc(LENGTH);
    buffer.length = LENGTH;

    uint8_t* ptr = buffer.data;
    serialize_g2_affine<Q, G2>(vk->alphaA_g2, ptr);
    serialize_g1_affine<Q, G1>(vk->alphaB_g1, ptr);
    serialize_g2_affine<Q, G2>(vk->alphaC_g2, ptr);
    serialize_g2_affine<Q, G2>(vk->gamma_g2, ptr);
    serialize_g1_affine<Q, G1>(vk->gamma_beta_g1, ptr);
    serialize_g2_affine<Q, G2>(vk->gamma_beta_g2, ptr);
    serialize_g2_affine<Q, G2>(vk->rC_Z_g2, ptr);
    serialize_g1_affine<Q, G1>(vk->encoded_IC_query.first, ptr);

    for (size_t i = 0; i < QUERY_COUNT; ++i)
        serialize_g1_affine<Q, G1>(vk->encoded_IC_query.rest.values[i], ptr);

    assert(ptr == buffer.data + buffer.length);
    return buffer;
}

template <mp_size_t Q, typename ppT, typename G1, typename G2>
buffer_t serialize_proof(r1cs_ppzksnark_proof<ppT>* proof)
{
    const size_t G1_SIZE = Q * sizeof(mp_limb_t) * 2; // [x, y]
    const size_t G2_SIZE = Q * sizeof(mp_limb_t) * 4; // [[x0, x1], [y0, y1]]

    const size_t LENGTH = (G1_SIZE * 7) + G2_SIZE;

    // [ ------------- LENGTH -------------- ]
    // [ a,  a_p,  b,  b_p,  c,  c_p,  h,  k ]

    buffer_t buffer;
    buffer.data = (uint8_t*)malloc(LENGTH);
    buffer.length = LENGTH;

    uint8_t* ptr = buffer.data;
    serialize_g1_affine<Q, G1>(proof->g_A.g, ptr);
    serialize_g1_affine<Q, G1>(proof->g_A.h, ptr);
    serialize_g2_affine<Q, G2>(proof->g_B.g, ptr);
    serialize_g1_affine<Q, G1>(proof->g_B.h, ptr);
    serialize_g1_affine<Q, G1>(proof->g_C.g, ptr);
    serialize_g1_affine<Q, G1>(proof->g_C.h, ptr);
    serialize_g1_affine<Q, G1>(proof->g_H, ptr);
    serialize_g1_affine<Q, G1>(proof->g_K, ptr);

    assert(ptr == buffer.data + buffer.length);
    return buffer;
}

template <mp_size_t Q, mp_size_t R, typename ppT, typename G1, typename G2>
setup_result_t setup(const uint8_t* a, const uint8_t* b, const uint8_t* c, int32_t a_len, int32_t b_len, int32_t c_len, int32_t constraints, int32_t variables, int32_t inputs)
{
    libff::inhibit_profiling_info = true;
    libff::inhibit_profiling_counters = true;

    // initialize curve parameters
    ppT::init_public_params();

    auto cs = create_constraint_system<r1cs_ppzksnark_constraint_system, R, ppT>(a, b, c, a_len, b_len, c_len, constraints, variables, inputs);
    assert(cs.num_variables() >= (unsigned)inputs);
    assert(cs.num_inputs() == (unsigned)inputs);
    assert(cs.num_constraints() == (unsigned)constraints);

    r1cs_ppzksnark_keypair<ppT> keypair = r1cs_ppzksnark_generator<ppT>(cs);

    buffer_t vk_buf = serialize_verification_key<Q, ppT, G1, G2>(&keypair.vk);
    buffer_t pk_buf = create_buffer(keypair.pk);

    setup_result_t result(vk_buf, pk_buf);
    return result;
}

template <mp_size_t Q, mp_size_t R, typename ppT, typename G1, typename G2>
proof_result_t generate_proof(buffer_t* pk_buf, const uint8_t* public_inputs, int32_t public_inputs_length, const uint8_t* private_inputs, int32_t private_inputs_length)
{
    libff::inhibit_profiling_info = true;
    libff::inhibit_profiling_counters = true;

    // initialize curve parameters
    ppT::init_public_params();

    r1cs_ppzksnark_proving_key<ppT> proving_key;
    from_buffer<r1cs_ppzksnark_proving_key<ppT>>(pk_buf, proving_key);

    // assign variables based on witness values, excludes ~one
    r1cs_variable_assignment<libff::Fr<ppT>> full_variable_assignment;
    for (int i = 1; i < public_inputs_length; i++) {
        full_variable_assignment.push_back(libff::Fr<ppT>(to_libff_bigint<R>(public_inputs + (i * R * sizeof(mp_limb_t)))));
    }
    for (int i = 0; i < private_inputs_length; i++) {
        full_variable_assignment.push_back(libff::Fr<ppT>(to_libff_bigint<R>(private_inputs + (i * R * sizeof(mp_limb_t)))));
    }

    r1cs_primary_input<libff::Fr<ppT>> primary_input(
        full_variable_assignment.begin(),
        full_variable_assignment.begin() + public_inputs_length - 1);

    r1cs_primary_input<libff::Fr<ppT>> auxiliary_input(
        full_variable_assignment.begin() + public_inputs_length - 1,
        full_variable_assignment.end());

    r1cs_ppzksnark_proof<ppT> proof = r1cs_ppzksnark_prover<ppT>(proving_key, primary_input, auxiliary_input);
    buffer_t proof_buf = serialize_proof<Q, ppT, G1, G2>(&proof);
    proof_result_t result(proof_buf);
    return result;
}

template <mp_size_t Q, mp_size_t R, typename ppT, typename G1, typename G2>
bool verify(buffer_t* vk_buf, buffer_t* proof_buf, const uint8_t* public_inputs, int32_t public_inputs_length)
{
    libff::inhibit_profiling_info = true;
    libff::inhibit_profiling_counters = true;

    // initialize curve parameters
    ppT::init_public_params();

    uint8_t* ptr = vk_buf->data;
    const G2 alphaA_g2 = deserialize_g2_affine<Q, typename ppT::Fqe_type, G2>(ptr);
    const G1 alphaB_g1 = deserialize_g1_affine<Q, typename ppT::Fq_type, G1>(ptr);
    const G2 alphaC_g2 = deserialize_g2_affine<Q, typename ppT::Fqe_type, G2>(ptr);
    const G2 gamma_g2 = deserialize_g2_affine<Q, typename ppT::Fqe_type, G2>(ptr);
    const G1 gamma_beta_g1 = deserialize_g1_affine<Q, typename ppT::Fq_type, G1>(ptr);
    const G2 gamma_beta_g2 = deserialize_g2_affine<Q, typename ppT::Fqe_type, G2>(ptr);
    const G2 rC_Z_g2 = deserialize_g2_affine<Q, typename ppT::Fqe_type, G2>(ptr);
    G1 ic_first = deserialize_g1_affine<Q, typename ppT::Fq_type, G1>(ptr);

    std::vector<G1> ic_rest;
    const size_t ic_rest_count = ((vk_buf->data + vk_buf->length) - ptr) / (Q * sizeof(mp_limb_t) * 2);
    for (size_t i = 0; i < ic_rest_count; i++) {
        auto ic_query = deserialize_g1_affine<Q, typename ppT::Fq_type, G1>(ptr);
        ic_rest.push_back(ic_query);
    }

    accumulation_vector<G1> eIC(std::move(ic_first), std::move(ic_rest));
    const r1cs_ppzksnark_verification_key<ppT> vk(alphaA_g2, alphaB_g1, alphaC_g2, gamma_g2, gamma_beta_g1, gamma_beta_g2, rC_Z_g2, eIC);

    ptr = proof_buf->data;
    const G1 g_A_g = deserialize_g1_affine<Q, typename ppT::Fq_type, G1>(ptr);
    const G1 g_A_h = deserialize_g1_affine<Q, typename ppT::Fq_type, G1>(ptr);
    const G2 g_B_g = deserialize_g2_affine<Q, typename ppT::Fqe_type, G2>(ptr);
    const G1 g_B_h = deserialize_g1_affine<Q, typename ppT::Fq_type, G1>(ptr);
    const G1 g_C_g = deserialize_g1_affine<Q, typename ppT::Fq_type, G1>(ptr);
    const G1 g_C_h = deserialize_g1_affine<Q, typename ppT::Fq_type, G1>(ptr);

    knowledge_commitment<G1, G1> g_A(g_A_g, g_A_h);
    knowledge_commitment<G2, G1> g_B(g_B_g, g_B_h);
    knowledge_commitment<G1, G1> g_C(g_C_g, g_C_h);

    G1 g_H = deserialize_g1_affine<Q, typename ppT::Fq_type, G1>(ptr);
    G1 g_K = deserialize_g1_affine<Q, typename ppT::Fq_type, G1>(ptr);

    const r1cs_ppzksnark_proof<ppT> proof(
        std::move(g_A),
        std::move(g_B),
        std::move(g_C),
        std::move(g_H),
        std::move(g_K));

    r1cs_primary_input<libff::Fr<ppT>> primary_input;
    for (int i = 0; i < public_inputs_length; i++) {
        primary_input.push_back(libff::Fr<ppT>(to_libff_bigint<R>(public_inputs + (i * R * sizeof(mp_limb_t)))));
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
    return pghr13::generate_proof<libff::alt_bn128_q_limbs,
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
    return pghr13::verify<libff::alt_bn128_q_limbs,
        libff::alt_bn128_r_limbs,
        libff::alt_bn128_pp,
        libff::alt_bn128_G1,
        libff::alt_bn128_G2>(vk_buf, proof_buf, public_inputs, public_inputs_length);
}