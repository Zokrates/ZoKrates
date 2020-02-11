/**
 * @file pghr13.cpp
 * @author Jacob Eberhardt <jacob.eberhardt@tu-berlin.de
 * @author Dennis Kuhnert <dennis.kuhnert@campus.tu-berlin.de>
 * @date 2017
 */

#include "util.hpp"
#include "pghr13.hpp"
#include <cassert>
#include <string>
#include <sstream>

// contains definitions of alt_bn128 ec public parameters
#include "libff/algebra/curves/alt_bn128/alt_bn128_pp.hpp"

// contains required interfaces and types (keypair, proof, generator, prover, verifier)
#include <libsnark/zk_proof_systems/ppzksnark/r1cs_ppzksnark/r1cs_ppzksnark.hpp>

typedef long integer_coeff_t;

using namespace libsnark;
using std::cout;
using std::endl;

namespace pghr13
{
    r1cs_ppzksnark_constraint_system<libff::alt_bn128_pp> createConstraintSystem(const uint8_t* A, const uint8_t* B, const uint8_t* C, int A_len, int B_len, int C_len, int constraints, int variables, int inputs)
    {
        r1cs_ppzksnark_constraint_system<libff::alt_bn128_pp> cs;
        cs.primary_input_size = inputs;
        cs.auxiliary_input_size = variables - inputs - 1; // ~one not included

        cout << "num variables: " << variables <<endl;
        cout << "num constraints: " << constraints <<endl;
        cout << "num inputs: " << inputs <<endl;

        struct VariableValueMapping {
            int constraint_id;
            int variable_id;
            uint8_t variable_value[32];
        };

        const VariableValueMapping* A_vvmap = (VariableValueMapping*) A;
        const VariableValueMapping* B_vvmap = (VariableValueMapping*) B;
        const VariableValueMapping* C_vvmap = (VariableValueMapping*) C;

        int A_id = 0;
        int B_id = 0;
        int C_id = 0;

        // initialize curve parameters
        libff::alt_bn128_pp::init_public_params();

        for (int row = 0; row < constraints; row++) {
            linear_combination<libff::Fr<libff::alt_bn128_pp> > lin_comb_A, lin_comb_B, lin_comb_C;
            while (A_id < A_len && A_vvmap[A_id].constraint_id == row) {
                libff::bigint<libff::alt_bn128_r_limbs> value = libsnarkBigintFromBytes(A_vvmap[A_id].variable_value);
                if (!value.is_zero()) {
                    lin_comb_A.add_term(A_vvmap[A_id].variable_id, value);
                }
                A_id++;
            }
            while (B_id < B_len && B_vvmap[B_id].constraint_id == row) {
                libff::bigint<libff::alt_bn128_r_limbs> value = libsnarkBigintFromBytes(B_vvmap[B_id].variable_value);
                if (!value.is_zero()) {
                    lin_comb_B.add_term(B_vvmap[B_id].variable_id, value);
                }
                B_id++;
            }
            while (C_id < C_len && C_vvmap[C_id].constraint_id == row) {
                libff::bigint<libff::alt_bn128_r_limbs> value = libsnarkBigintFromBytes(C_vvmap[C_id].variable_value);
                if (!value.is_zero()) {
                    lin_comb_C.add_term(C_vvmap[C_id].variable_id, value);
                }
                C_id++;
            }
            cs.add_constraint(r1cs_constraint<libff::Fr<libff::alt_bn128_pp> >(lin_comb_A, lin_comb_B, lin_comb_C));
        }
        return cs;
    }

    r1cs_ppzksnark_keypair<libff::alt_bn128_pp> generateKeypair(const r1cs_ppzksnark_constraint_system<libff::alt_bn128_pp> &cs) {
        return r1cs_ppzksnark_generator<libff::alt_bn128_pp>(cs); // from r1cs_ppzksnark.hpp
    }

    std::string serializeVerificationKey(r1cs_ppzksnark_verification_key<libff::alt_bn128_pp>* vk)
    {
        std::stringstream ss;
        unsigned icLength = vk->encoded_IC_query.rest.indices.size() + 1;

        ss << "vk.a = " << outputPointG2AffineAsHex(vk->alphaA_g2) << endl;
        ss << "vk.b = " << outputPointG1AffineAsHex(vk->alphaB_g1) << endl;
        ss << "vk.c = " << outputPointG2AffineAsHex(vk->alphaC_g2) << endl;
        ss << "vk.gamma = " << outputPointG2AffineAsHex(vk->gamma_g2) << endl;
        ss << "vk.gamma_beta_1 = " << outputPointG1AffineAsHex(vk->gamma_beta_g1) << endl;
        ss << "vk.gamma_beta_2 = " << outputPointG2AffineAsHex(vk->gamma_beta_g2) << endl;
        ss << "vk.z = " << outputPointG2AffineAsHex(vk->rC_Z_g2) << endl;
        ss << "vk.ic.len() = " << icLength << endl;
        ss << "vk.ic[0] = " << outputPointG1AffineAsHex(vk->encoded_IC_query.first) << endl;
        for (size_t i = 1; i < icLength; ++i)
        {
            auto vk_ic_i = outputPointG1AffineAsHex(vk->encoded_IC_query.rest.values[i - 1]);
            ss << "vk.ic[" << i << "] = " << vk_ic_i << endl;
        }
        std::string str = ss.str();
        return str;
    }

    std::string serializeProof(r1cs_ppzksnark_proof<libff::alt_bn128_pp>* proof, const uint8_t* public_inputs, int public_inputs_length)
    {
        std::stringstream ss;
        ss << "{" << "\n";
        ss << "\t\"proof\": {" << "\n";
        ss << "\t\t\"a\": " << outputPointG1AffineAsHexJson(proof->g_A.g) << ",\n";
        ss << "\t\t\"a_p\": " << outputPointG1AffineAsHexJson(proof->g_A.h) << ",\n";
        ss << "\t\t\"b\": " << outputPointG2AffineAsHexJson(proof->g_B.g) << ",\n";
        ss << "\t\t\"b_p\": " << outputPointG1AffineAsHexJson(proof->g_B.h) << ",\n";
        ss << "\t\t\"c\": " << outputPointG1AffineAsHexJson(proof->g_C.g) << ",\n";
        ss << "\t\t\"c_p\": " << outputPointG1AffineAsHexJson(proof->g_C.h) << ",\n";
        ss << "\t\t\"h\": " << outputPointG1AffineAsHexJson(proof->g_H) << ",\n";
        ss << "\t\t\"k\": " << outputPointG1AffineAsHexJson(proof->g_K) << "\n";
        ss << "\t}," << "\n";
        ss << "\t\"inputs\": " << "[";
        for (int i = 1; i < public_inputs_length; i++) {
            if (i != 1) {
                ss << ",";
            }
            ss << outputInputAsHex(libsnarkBigintFromBytes(public_inputs + i * 32));
        }
        ss << "]" << "\n";
        ss << "}" << "\n";
        std::string str = ss.str();
        return str;
    }
}

setup_result_t pghr13_setup(const uint8_t* A, const uint8_t* B, const uint8_t* C, int32_t A_len, int32_t B_len, int32_t C_len, int32_t constraints, int32_t variables, int32_t inputs)
{
    libff::inhibit_profiling_info = true;
    libff::inhibit_profiling_counters = true;

    // initialize curve parameters
    libff::alt_bn128_pp::init_public_params();

    auto cs = pghr13::createConstraintSystem(A, B, C, A_len, B_len, C_len, constraints, variables, inputs);

    assert(cs.num_variables() >= (unsigned)inputs);
    assert(cs.num_inputs() == (unsigned)inputs);
    assert(cs.num_constraints() == (unsigned)constraints);

    // create keypair
    auto keypair = r1cs_ppzksnark_generator<libff::alt_bn128_pp>(cs);
    auto vk = pghr13::serializeVerificationKey(&keypair.vk);

    std::stringstream ss;
    ss << keypair.pk;

    std::string pk = ss.str();

    buffer_t vk_buf, pk_buf;
    __alloc(&vk_buf, vk.size());
    __alloc(&pk_buf, pk.size());

    vk.copy(reinterpret_cast<char*>(vk_buf.data), vk_buf.length);
    pk.copy(reinterpret_cast<char*>(pk_buf.data), pk_buf.length);

    setup_result_t result(vk_buf, pk_buf);
    return result;
}

proof_result_t pghr13_generate_proof(buffer_t* pk_buf, const uint8_t* public_inputs, int32_t public_inputs_length, const uint8_t* private_inputs, int32_t private_inputs_length)
{
    libff::inhibit_profiling_info = true;
    libff::inhibit_profiling_counters = true;

    // initialize curve parameters
    libff::alt_bn128_pp::init_public_params();
    r1cs_ppzksnark_proving_key<libff::alt_bn128_pp> proving_key;

    std::stringstream ss;
    ss.write(reinterpret_cast<const char*>(pk_buf->data), pk_buf->length);
    ss.rdbuf()->pubseekpos(0, std::ios_base::in);
    ss >> proving_key;

    // assign variables based on witness values, excludes ~one
    r1cs_variable_assignment<libff::Fr<libff::alt_bn128_pp> > full_variable_assignment;
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
    auto proof = r1cs_ppzksnark_prover<libff::alt_bn128_pp>(proving_key, primary_input, auxiliary_input);
    auto proof_json = pghr13::serializeProof(&proof, public_inputs, public_inputs_length);

    buffer_t proof_buf;
    __alloc(&proof_buf, proof_json.size());

    proof_json.copy(reinterpret_cast<char*>(proof_buf.data), proof_buf.length);
    proof_result_t result(proof_buf);
    return result;
}
