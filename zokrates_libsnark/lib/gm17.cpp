/**
 * @file gm17.cpp
 * @author Jacob Eberhardt <jacob.eberhardt@tu-berlin.de
 * @author Dennis Kuhnert <dennis.kuhnert@campus.tu-berlin.de>
 * @date 2017
 */

#include "gm17.hpp"

#include <cassert>
#include <sstream>
#include <string>

// contains definition of alt_bn128 ec public parameters
#include "libff/algebra/curves/alt_bn128/alt_bn128_pp.hpp"

// contains required interfaces and types (keypair, proof, generator, prover, verifier)
#include <libsnark/zk_proof_systems/ppzksnark/r1cs_se_ppzksnark/r1cs_se_ppzksnark.hpp>

using namespace libsnark;

#include "util.tcc"

namespace gm17 {

template <mp_size_t Q, typename ppT, typename G1, typename G2>
buffer_t serialize_verification_key(r1cs_se_ppzksnark_verification_key<ppT>* vk)
{
    const size_t QUERY_COUNT = vk->query.size();

    const size_t G1_SIZE = Q * sizeof(mp_limb_t) * 2; // [x, y]
    const size_t G2_SIZE = Q * sizeof(mp_limb_t) * 4; // [[x0, x1], [y0, y1]]

    const size_t LENGTH = (G1_SIZE * 2) + (G2_SIZE * 3) + (QUERY_COUNT * G1_SIZE);

    // [ ----------------- LENGTH ------------------ ]
    // [ h, G_alpha, H_beta, G_gamma, H_gamma, query ]

    buffer_t buffer;
    buffer.data = (uint8_t*)malloc(LENGTH);
    buffer.length = LENGTH;

    uint8_t* ptr = buffer.data;
    serialize_g2_affine<Q, G2>(vk->H, ptr);
    serialize_g1_affine<Q, G1>(vk->G_alpha, ptr);
    serialize_g2_affine<Q, G2>(vk->H_beta, ptr);
    serialize_g1_affine<Q, G1>(vk->G_gamma, ptr);
    serialize_g2_affine<Q, G2>(vk->H_gamma, ptr);

    for (size_t i = 0; i < QUERY_COUNT; ++i)
        serialize_g1_affine<Q, G1>(vk->query[i], ptr);

    assert(ptr == buffer.data + buffer.length);
    return buffer;
}

template <mp_size_t Q, typename ppT, typename G1, typename G2>
buffer_t serialize_proof(r1cs_se_ppzksnark_proof<ppT>* proof)
{
    const size_t G1_SIZE = Q * sizeof(mp_limb_t) * 2; // [x, y]
    const size_t G2_SIZE = Q * sizeof(mp_limb_t) * 4; // [[x0, x1], [y0, y1]]

    const size_t LENGTH = (G1_SIZE * 2) + G2_SIZE;

    // [ ---------- LENGTH ---------- ]
    // [ G1_SIZE,  G2_SIZE,  G1_SIZE  ]
    // [ a,        b,        c        ]

    buffer_t buffer;
    buffer.data = (uint8_t*)malloc(LENGTH);
    buffer.length = LENGTH;

    uint8_t* ptr = buffer.data;
    serialize_g1_affine<Q, G1>(proof->A, ptr);
    serialize_g2_affine<Q, G2>(proof->B, ptr);
    serialize_g1_affine<Q, G1>(proof->C, ptr);

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

    auto cs = create_constraint_system<r1cs_se_ppzksnark_constraint_system, R, ppT>(a, b, c, a_len, b_len, c_len, constraints, variables, inputs);
    assert(cs.num_variables() >= (unsigned)inputs);
    assert(cs.num_inputs() == (unsigned)inputs);
    assert(cs.num_constraints() == (unsigned)constraints);

    r1cs_se_ppzksnark_keypair<ppT> keypair = r1cs_se_ppzksnark_generator<ppT>(cs);

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

    r1cs_se_ppzksnark_proving_key<ppT> proving_key;
    from_buffer<r1cs_se_ppzksnark_proving_key<ppT>>(pk_buf, proving_key);

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

    r1cs_se_ppzksnark_proof<ppT> proof = r1cs_se_ppzksnark_prover<ppT>(proving_key, primary_input, auxiliary_input);
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
    const G2 H = deserialize_g2_affine<Q, typename ppT::Fqe_type, G2>(ptr);
    const G1 G_alpha = deserialize_g1_affine<Q, typename ppT::Fq_type, G1>(ptr);
    const G2 H_beta = deserialize_g2_affine<Q, typename ppT::Fqe_type, G2>(ptr);
    const G1 G_gamma = deserialize_g1_affine<Q, typename ppT::Fq_type, G1>(ptr);
    const G2 H_gamma = deserialize_g2_affine<Q, typename ppT::Fqe_type, G2>(ptr);

    libff::G1_vector<ppT> query_G1_vector;

    const size_t query_count = ((vk_buf->data + vk_buf->length) - ptr) / (Q * sizeof(mp_limb_t) * 2);
    for (size_t i = 0; i < query_count; i++) {
        auto query = deserialize_g1_affine<Q, typename ppT::Fq_type, G1>(ptr);
        query_G1_vector.push_back(query);
    }

    const r1cs_se_ppzksnark_verification_key<ppT> vk(H, G_alpha, H_beta, G_gamma, H_gamma, std::move(query_G1_vector));

    ptr = proof_buf->data;
    G1 a = deserialize_g1_affine<Q, typename ppT::Fq_type, G1>(ptr);
    G2 b = deserialize_g2_affine<Q, typename ppT::Fqe_type, G2>(ptr);
    G1 c = deserialize_g1_affine<Q, typename ppT::Fq_type, G1>(ptr);
    r1cs_se_ppzksnark_proof<ppT> proof(
        std::move(a),
        std::move(b),
        std::move(c));

    r1cs_primary_input<libff::Fr<ppT>> primary_input;
    for (int i = 0; i < public_inputs_length; i++) {
        primary_input.push_back(libff::Fr<ppT>(to_libff_bigint<R>(public_inputs + (i * R * sizeof(mp_limb_t)))));
    }

    return r1cs_se_ppzksnark_verifier_strong_IC<ppT>(vk, primary_input, proof);
}
}

setup_result_t gm17_bn128_setup(const uint8_t* a, const uint8_t* b, const uint8_t* c, int32_t a_len, int32_t b_len, int32_t c_len, int32_t constraints, int32_t variables, int32_t inputs)
{
    return gm17::setup<libff::alt_bn128_q_limbs,
        libff::alt_bn128_r_limbs,
        libff::alt_bn128_pp,
        libff::alt_bn128_G1,
        libff::alt_bn128_G2>(a, b, c, a_len, b_len, c_len, constraints, variables, inputs);
}

proof_result_t gm17_bn128_generate_proof(buffer_t* pk_buf,
    const uint8_t* public_inputs,
    int32_t public_inputs_length,
    const uint8_t* private_inputs,
    int32_t private_inputs_length)
{
    return gm17::generate_proof<libff::alt_bn128_q_limbs,
        libff::alt_bn128_r_limbs,
        libff::alt_bn128_pp,
        libff::alt_bn128_G1,
        libff::alt_bn128_G2>(pk_buf,
        public_inputs,
        public_inputs_length,
        private_inputs,
        private_inputs_length);
}

bool gm17_bn128_verify(buffer_t* vk_buf, buffer_t* proof_buf, const uint8_t* public_inputs, int32_t public_inputs_length)
{
    return gm17::verify<libff::alt_bn128_q_limbs,
        libff::alt_bn128_r_limbs,
        libff::alt_bn128_pp,
        libff::alt_bn128_G1,
        libff::alt_bn128_G2>(vk_buf, proof_buf, public_inputs, public_inputs_length);
}