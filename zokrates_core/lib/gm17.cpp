/**
 * @file wraplibsnark.cpp
 * @author Jacob Eberhardt <jacob.eberhardt@tu-berlin.de
 * @author Dennis Kuhnert <dennis.kuhnert@campus.tu-berlin.de>
 * @date 2017
 */

#include "util.hpp"
#include "gm17.hpp"
#include <cassert>
#include <iomanip>

// contains definition of alt_bn128 ec public parameters
#include "libff/algebra/curves/alt_bn128/alt_bn128_pp.hpp"
// contains required interfaces and types (keypair, proof, generator, prover, verifier)
#include <libsnark/zk_proof_systems/ppzksnark/r1cs_se_ppzksnark/r1cs_se_ppzksnark.hpp>

typedef long integer_coeff_t;

using namespace std;
using namespace libsnark;

namespace gm17 
{
  //takes input and puts it into constraint system
  r1cs_se_ppzksnark_constraint_system<libff::alt_bn128_pp> createConstraintSystem(const uint8_t* A, const uint8_t* B, const uint8_t* C, int A_len, int B_len, int C_len, int constraints, int variables, int inputs)
  {
    r1cs_se_ppzksnark_constraint_system<libff::alt_bn128_pp> cs;
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

    libff::alt_bn128_pp::init_public_params();

    for (int row = 0; row < constraints; row++) {
      linear_combination<libff::Fr<libff::alt_bn128_pp> > lin_comb_A, lin_comb_B, lin_comb_C;

      while (A_id < A_len && A_vvmap[A_id].constraint_id == row) {
        libff::bigint<libff::alt_bn128_r_limbs> value = libsnarkBigintFromBytes(A_vvmap[A_id].variable_value);
        if (!value.is_zero())
          lin_comb_A.add_term(A_vvmap[A_id].variable_id, value);
        A_id++;
      }
      while (B_id < B_len && B_vvmap[B_id].constraint_id == row) {
        libff::bigint<libff::alt_bn128_r_limbs> value = libsnarkBigintFromBytes(B_vvmap[B_id].variable_value);
        if (!value.is_zero())
          lin_comb_B.add_term(B_vvmap[B_id].variable_id, value);
        B_id++;
      }
      while (C_id < C_len && C_vvmap[C_id].constraint_id == row) {
        libff::bigint<libff::alt_bn128_r_limbs> value = libsnarkBigintFromBytes(C_vvmap[C_id].variable_value);
        if (!value.is_zero())
          lin_comb_C.add_term(C_vvmap[C_id].variable_id, value);
        C_id++;
      }

      cs.add_constraint(r1cs_constraint<libff::Fr<libff::alt_bn128_pp> >(lin_comb_A, lin_comb_B, lin_comb_C));
    }
    return cs;
  }

  // keypair generateKeypair(constraints)
  r1cs_se_ppzksnark_keypair<libff::alt_bn128_pp> generateKeypair(const r1cs_se_ppzksnark_constraint_system<libff::alt_bn128_pp> &cs)
  {
    // from r1cs_se_ppzksnark.hpp
    return r1cs_se_ppzksnark_generator<libff::alt_bn128_pp>(cs);
  }

  std::string serializeVerificationKey(r1cs_se_ppzksnark_verification_key<libff::alt_bn128_pp>* vk)
  {
    std::stringstream ss;
    unsigned queryLength = vk->query.size();

    ss << "\t\tvk.h = " << outputPointG2AffineAsHex(vk->H) << endl;
    ss << "\t\tvk.g_alpha = " << outputPointG1AffineAsHex(vk->G_alpha) << endl;
    ss << "\t\tvk.h_beta = " << outputPointG2AffineAsHex(vk->H_beta) << endl;
    ss << "\t\tvk.g_gamma = " << outputPointG1AffineAsHex(vk->G_gamma) << endl;
    ss << "\t\tvk.h_gamma = " << outputPointG2AffineAsHex(vk->H_gamma) << endl;
    ss << "\t\tvk.query.len() = " << queryLength << endl;
    for (size_t i = 0; i < queryLength; ++i)
    {
        auto vkqueryi = outputPointG1AffineAsHex(vk->query[i]);
        ss << "\t\tvk.query[" << i << "] = " << vkqueryi << endl;
    }
    return ss.str();
  }

  std::string exportProof(r1cs_se_ppzksnark_proof<libff::alt_bn128_pp> proof, const uint8_t* public_inputs, int public_inputs_length)
  {
    std::stringstream ss;
    ss << "{" << "\n";
      ss << "\t\"proof\":" << "\n";
        ss << "\t{" << "\n";
          ss << "\t\t\"a\":" <<outputPointG1AffineAsHexJson(proof.A) << ",\n";
          ss << "\t\t\"b\":" << "\n";
            ss << "\t\t\t" << outputPointG2AffineAsHexJson(proof.B) << ",\n";
          ss << "\t\t\n";
          ss << "\t\t\"c\":" <<outputPointG1AffineAsHexJson(proof.C) << "\n";
        ss << "\t}," << "\n";
      //add input to json
      ss << "\t\"inputs\":" << "[";
      for (int i = 1; i < public_inputs_length; i++) {
        if(i!=1){
          ss << ",";
        }
        ss << outputInputAsHex(libsnarkBigintFromBytes(public_inputs + i*32));
      }
      ss << "]" << "\n";
    ss << "}" << "\n";
    return ss.str();
  }
}

void _gm17_setup(const uint8_t* A, const uint8_t* B, const uint8_t* C, int A_len, int B_len, int C_len, int constraints, int variables, int inputs, uint8_t* vk_buf, uint8_t* pk_buf)
{
  libff::inhibit_profiling_info = true;
  libff::inhibit_profiling_counters = true;

  //initialize curve parameters
  libff::alt_bn128_pp::init_public_params();

  auto cs = gm17::createConstraintSystem(A, B, C, A_len, B_len, C_len, constraints, variables, inputs);

  assert(cs.num_variables() >= (unsigned)inputs);
  assert(cs.num_inputs() == (unsigned)inputs);
  assert(cs.num_constraints() == (unsigned)constraints);

  // create keypair
  auto keypair = r1cs_se_ppzksnark_generator<libff::alt_bn128_pp>(cs);
  auto vk = gm17::serializeVerificationKey(&keypair.vk);
  
  std::stringstream ss;
  ss << keypair.pk;

  std::string pk = ss.str();
  memcpy(pk_buf, pk.c_str(), pk.size());
  memcpy(vk_buf, vk.c_str(), vk.size());
}

void _gm17_generate_proof(const uint8_t* pk_buf, int pk_buf_length, const uint8_t* public_inputs, int public_inputs_length, const uint8_t* private_inputs, int private_inputs_length, uint8_t* proof_buf)
{
  libff::inhibit_profiling_info = true;
  libff::inhibit_profiling_counters = true;

  //initialize curve parameters
  libff::alt_bn128_pp::init_public_params();
  r1cs_se_ppzksnark_proving_key<libff::alt_bn128_pp> pk;

  std::stringstream ss;
  ss.write(reinterpret_cast<const char*>(pk_buf), pk_buf_length);
  ss.rdbuf()->pubseekpos(0, std::ios_base::in);
  ss >> pk;

  // assign variables based on witness values, excludes ~one
  r1cs_variable_assignment<libff::Fr<libff::alt_bn128_pp> > full_variable_assignment;
  for (int i = 1; i < public_inputs_length; i++) {
    full_variable_assignment.push_back(libff::Fr<libff::alt_bn128_pp>(libsnarkBigintFromBytes(public_inputs + i*32)));
  }
  for (int i = 0; i < private_inputs_length; i++) {
    full_variable_assignment.push_back(libff::Fr<libff::alt_bn128_pp>(libsnarkBigintFromBytes(private_inputs + i*32)));
  }

  // split up variables into primary and auxiliary inputs. Does *NOT* include the constant 1
  // Public variables belong to primary input, private variables are auxiliary input.
  r1cs_primary_input<libff::Fr<libff::alt_bn128_pp>> primary_input(full_variable_assignment.begin(), full_variable_assignment.begin() + public_inputs_length-1);
  r1cs_primary_input<libff::Fr<libff::alt_bn128_pp>> auxiliary_input(full_variable_assignment.begin() + public_inputs_length-1, full_variable_assignment.end());

  // for debugging
  // cout << "full variable assignment:"<< endl << full_variable_assignment;
  // cout << "primary input:"<< endl << primary_input;
  // cout << "auxiliary input:"<< endl << auxiliary_input;

  // Proof Generation
  auto proof = r1cs_se_ppzksnark_prover<libff::alt_bn128_pp>(pk, primary_input, auxiliary_input);
  auto result = gm17::exportProof(proof, public_inputs, public_inputs_length);
  memcpy(proof_buf, result.c_str(), result.size());
}