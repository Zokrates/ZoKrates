/**
 * @file wraplibsnark.cpp
 * @author Jacob Eberhardt <jacob.eberhardt@tu-berlin.de
 * @author Dennis Kuhnert <dennis.kuhnert@campus.tu-berlin.de>
 * @date 2017
 */

#include "util.hpp"
#include "pghr13.hpp"
#include <fstream>
#include <iostream>
#include <cassert>
#include <iomanip>

// contains definition of alt_bn128 ec public parameters
#include "libff/algebra/curves/alt_bn128/alt_bn128_pp.hpp"
// contains required interfaces and types (keypair, proof, generator, prover, verifier)
#include <libsnark/zk_proof_systems/ppzksnark/r1cs_ppzksnark/r1cs_ppzksnark.hpp>

typedef long integer_coeff_t;

using namespace std;
using namespace libsnark;

namespace pghr13 {

//takes input and puts it into constraint system
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
r1cs_ppzksnark_keypair<libff::alt_bn128_pp> generateKeypair(const r1cs_ppzksnark_constraint_system<libff::alt_bn128_pp> &cs){
  // from r1cs_ppzksnark.hpp
  return r1cs_ppzksnark_generator<libff::alt_bn128_pp>(cs);
}

void serializeProvingKeyToFile(r1cs_ppzksnark_proving_key<libff::alt_bn128_pp> pk, const char* pk_path){
  writeToFile(pk_path, pk);
}

void serializeR1CSToFile(std::string r1cs, const char* r1cs_path){
  writeToFile(r1cs_path, r1cs);
}

r1cs_ppzksnark_proving_key<libff::alt_bn128_pp> deserializeProvingKeyFromFile(const char* pk_path){
  return loadFromFile<r1cs_ppzksnark_proving_key<libff::alt_bn128_pp>>(pk_path);
}

std::string serializeOneTerm(linear_term<libff::Fr<libff::alt_bn128_pp>> term) {
     std::stringstream ss;

    ss << "{" << endl;
    ss << "\"index\":" << term.index << "," << endl;
    ss << "\"value\":" << "\"" << HexStringFromLibsnarkBigint(term.coeff.as_bigint()) << "\"" << endl;
    ss << "}";

    return ss.str();

}

std::string serializeTerms(std::vector<linear_term<libff::Fr<libff::alt_bn128_pp>> > terms) {
     std::stringstream ss;

     for (size_t i = 0; i < terms.size(); i++) {
        linear_term<libff::Fr<libff::alt_bn128_pp>> term = terms[i];
         ss << pghr13::serializeOneTerm(term);

         if (i + 1 < terms.size()) {
             ss << "," << endl;
         } else {
             ss << endl;
         }
     }

      return ss.str();
}

std::string serializeLinearCombination(std::string field,
     linear_combination<libff::Fr<libff::alt_bn128_pp>> combination,
     bool addCommaSeparator) {

     std::stringstream ss;

     ss << "\"" << field << "\": [" << endl;
     ss << pghr13::serializeTerms(combination.terms);
     ss << "]";
     if (addCommaSeparator) {
          ss << ",";
     }
     ss << endl;

     return ss.str();
}

std::string serializeOneConstraint(r1cs_constraint<libff::Fr<libff::alt_bn128_pp>> constraint) {
    std::stringstream ss;
    ss << "{" << endl;
    ss << pghr13::serializeLinearCombination("A", constraint.a, true);
    ss << pghr13::serializeLinearCombination("B", constraint.b, true);
    ss << pghr13::serializeLinearCombination("C", constraint.c, false);
    ss << "}";

    return ss.str();
}


std::string serializeConstraints(std::vector<r1cs_constraint<libff::Fr<libff::alt_bn128_pp>> > constraints) {
        std::stringstream ss;

        ss << "[" << endl;

        for (size_t i = 0; i < constraints.size(); i++) {
            r1cs_constraint<libff::Fr<libff::alt_bn128_pp>> constraint = constraints[i];
            ss << pghr13::serializeOneConstraint(constraint);
            if (i + 1 < constraints.size()) {
                ss << "," << endl;
            } else {
                ss << endl;
            }
        }
        ss << "]";
     return ss.str();
}


std::string serializeR1CS(r1cs_ppzksnark_constraint_system<libff::alt_bn128_pp> cs) {
    std::stringstream ss;

    ss << "{" << endl;
    ss << "\"primary_input_size\": " << cs.primary_input_size << "," << endl;
    ss << "\"auxiliary_input_size\": " << cs.auxiliary_input_size << "," << endl;
    ss << "\"constraints\": " << pghr13::serializeConstraints(cs.constraints) << endl;
    ss << "}" << endl;

    return ss.str();
}


void serializeVerificationKeyToFile(r1cs_ppzksnark_verification_key<libff::alt_bn128_pp> vk, const char* vk_path){
  std::stringstream ss;

  unsigned icLength = vk.encoded_IC_query.rest.indices.size() + 1;

  ss << "\t\tvk.A = " << outputPointG2AffineAsHex(vk.alphaA_g2) << endl;
  ss << "\t\tvk.B = " << outputPointG1AffineAsHex(vk.alphaB_g1) << endl;
  ss << "\t\tvk.C = " << outputPointG2AffineAsHex(vk.alphaC_g2) << endl;
  ss << "\t\tvk.gamma = " << outputPointG2AffineAsHex(vk.gamma_g2) << endl;
  ss << "\t\tvk.gammaBeta1 = " << outputPointG1AffineAsHex(vk.gamma_beta_g1) << endl;
  ss << "\t\tvk.gammaBeta2 = " << outputPointG2AffineAsHex(vk.gamma_beta_g2) << endl;
  ss << "\t\tvk.Z = " << outputPointG2AffineAsHex(vk.rC_Z_g2) << endl;
  ss << "\t\tvk.IC.len() = " << icLength << endl;
  ss << "\t\tvk.IC[0] = " << outputPointG1AffineAsHex(vk.encoded_IC_query.first) << endl;
  for (size_t i = 1; i < icLength; ++i)
  {
                  auto vkICi = outputPointG1AffineAsHex(vk.encoded_IC_query.rest.values[i - 1]);
                  ss << "\t\tvk.IC[" << i << "] = " << vkICi << endl;
  }

  std::ofstream fh;
  fh.open(vk_path, std::ios::binary);
  ss.rdbuf()->pubseekpos(0, std::ios_base::out);
  fh << ss.rdbuf();
  fh.flush();
  fh.close();
}

// compliant with solidty verification example
void exportVerificationKey(r1cs_ppzksnark_keypair<libff::alt_bn128_pp> keypair){
        auto vk = keypair.vk;
        unsigned icLength = vk.encoded_IC_query.rest.indices.size() + 1;

        cout << "\tVerification key in Solidity compliant format:{" << endl;
        cout << "\t\tvk.A = Pairing.G2Point(" << outputPointG2AffineAsHex(vk.alphaA_g2) << ");" << endl;
        cout << "\t\tvk.B = Pairing.G1Point(" << outputPointG1AffineAsHex(vk.alphaB_g1) << ");" << endl;
        cout << "\t\tvk.C = Pairing.G2Point(" << outputPointG2AffineAsHex(vk.alphaC_g2) << ");" << endl;
        cout << "\t\tvk.gamma = Pairing.G2Point(" << outputPointG2AffineAsHex(vk.gamma_g2) << ");" << endl;
        cout << "\t\tvk.gammaBeta1 = Pairing.G1Point(" << outputPointG1AffineAsHex(vk.gamma_beta_g1) << ");" << endl;
        cout << "\t\tvk.gammaBeta2 = Pairing.G2Point(" << outputPointG2AffineAsHex(vk.gamma_beta_g2) << ");" << endl;
        cout << "\t\tvk.Z = Pairing.G2Point(" << outputPointG2AffineAsHex(vk.rC_Z_g2) << ");" << endl;
        cout << "\t\tvk.IC = new Pairing.G1Point[](" << icLength << ");" << endl;
        cout << "\t\tvk.IC[0] = Pairing.G1Point(" << outputPointG1AffineAsHex(vk.encoded_IC_query.first) << ");" << endl;
        for (size_t i = 1; i < icLength; ++i)
        {
                auto vkICi = outputPointG1AffineAsHex(vk.encoded_IC_query.rest.values[i - 1]);
                cout << "\t\tvk.IC[" << i << "] = Pairing.G1Point(" << vkICi << ");" << endl;
        }
        cout << "\t\t}" << endl;

}

void printProof(r1cs_ppzksnark_proof<libff::alt_bn128_pp> proof, const char* proof_path, const uint8_t* public_inputs,
            int public_inputs_length){
                cout << "Proof:"<< endl;
                cout << "A = Pairing.G1Point(" << outputPointG1AffineAsHex(proof.g_A.g)<< ");" << endl;
                cout << "A_p = Pairing.G1Point(" << outputPointG1AffineAsHex(proof.g_A.h)<< ");" << endl;
                cout << "B = Pairing.G2Point(" << outputPointG2AffineAsHex(proof.g_B.g)<< ");" << endl;
                cout << "B_p = Pairing.G1Point(" << outputPointG1AffineAsHex(proof.g_B.h)<<");" << endl;
                cout << "C = Pairing.G1Point(" << outputPointG1AffineAsHex(proof.g_C.g)<< ");" << endl;
                cout << "C_p = Pairing.G1Point(" << outputPointG1AffineAsHex(proof.g_C.h)<<");" << endl;
                cout << "H = Pairing.G1Point(" << outputPointG1AffineAsHex(proof.g_H)<<");"<< endl;
                cout << "K = Pairing.G1Point(" << outputPointG1AffineAsHex(proof.g_K)<<");"<< endl;

                //create JSON file
                std::stringstream ss;
                ss << "{" << "\n";
                  ss << "\t\"proof\":" << "\n";
                    ss << "\t{" << "\n";
                      ss << "\t\t\"A\":" <<outputPointG1AffineAsHexJson(proof.g_A.g) << ",\n";
                      ss << "\t\t\"A_p\":" <<outputPointG1AffineAsHexJson(proof.g_A.h) << ",\n";
                      ss << "\t\t\"B\":" << "\n";
                        ss << "\t\t\t" << outputPointG2AffineAsHexJson(proof.g_B.g) << ",\n";
                      ss << "\t\t\n";
                      ss << "\t\t\"B_p\":" <<outputPointG1AffineAsHexJson(proof.g_B.h) << ",\n";
                      ss << "\t\t\"C\":" <<outputPointG1AffineAsHexJson(proof.g_C.g) << ",\n";
                      ss << "\t\t\"C_p\":" <<outputPointG1AffineAsHexJson(proof.g_C.h) << ",\n";
                      ss << "\t\t\"H\":" <<outputPointG1AffineAsHexJson(proof.g_H) << ",\n";
                      ss << "\t\t\"K\":" <<outputPointG1AffineAsHexJson(proof.g_K) << "\n";
                    ss << "\t}," << "\n";
                  //add input to json
                  ss << "\t\"input\":" << "[";
                  for (int i = 1; i < public_inputs_length; i++) {
                    if(i!=1){
                      ss << ",";
                    }
                    ss << libsnarkBigintFromBytes(public_inputs + i*32);
                  }
                  ss << "]" << "\n";
                ss << "}" << "\n";

                std::string s = ss.str();
                //write json string to proof_path
                writeToFile(proof_path, s);
}

}

// compliant with solidty verification example
void exportInput(r1cs_primary_input<libff::Fr<libff::alt_bn128_pp>> input){
        cout << "\tInput in Solidity compliant format:{" << endl;
        for (size_t i = 0; i < input.size(); ++i)
        {
                cout << "\t\tinput[" << i << "] = " << HexStringFromLibsnarkBigint(input[i].as_bigint()) << ";" << endl;
        }
        cout << "\t\t}" << endl;
}

bool _pghr13_setup(const uint8_t* A, const uint8_t* B, const uint8_t* C, int A_len, int B_len, int C_len, int constraints, int variables, int inputs, const char* pk_path, const char* vk_path, const char* r1cs_path)
{
  libff::inhibit_profiling_info = true;
  libff::inhibit_profiling_counters = true;

  //initialize curve parameters
  libff::alt_bn128_pp::init_public_params();

  auto cs = pghr13::createConstraintSystem(A, B, C, A_len, B_len, C_len, constraints, variables, inputs);

  assert(cs.num_variables() >= (unsigned)inputs);
  assert(cs.num_inputs() == (unsigned)inputs);
  assert(cs.num_constraints() == (unsigned)constraints);

  // create keypair
  auto keypair = r1cs_ppzksnark_generator<libff::alt_bn128_pp>(cs);

  // Export vk and pk to files
  pghr13::serializeProvingKeyToFile(keypair.pk, pk_path);
  pghr13::serializeVerificationKeyToFile(keypair.vk, vk_path);
  pghr13::serializeR1CSToFile(pghr13::serializeR1CS(cs), r1cs_path);

  // Print VerificationKey in Solidity compatible format
  pghr13::exportVerificationKey(keypair);

  return true;
}

bool _pghr13_generate_proof(const char* pk_path, const char* proof_path, const uint8_t* public_inputs, int public_inputs_length, const uint8_t* private_inputs, int private_inputs_length)
{
  libff::inhibit_profiling_info = true;
  libff::inhibit_profiling_counters = true;

  //initialize curve parameters
  libff::alt_bn128_pp::init_public_params();
  auto pk = pghr13::deserializeProvingKeyFromFile(pk_path);

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
  auto proof = r1cs_ppzksnark_prover<libff::alt_bn128_pp>(pk, primary_input, auxiliary_input);

  // print proof
  pghr13::printProof(proof, proof_path, public_inputs, public_inputs_length);
  // TODO? print inputs

  return true;
}
