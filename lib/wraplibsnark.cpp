/**
 * @file wraplibsnark.cpp
 * @author Jacob Eberhardt <jacob.eberhardt@tu-berlin.de
 * @author Dennis Kuhnert <dennis.kuhnert@campus.tu-berlin.de>
 * @date 2017
 */

#include "wraplibsnark.hpp"
#include <fstream>
#include <iostream>
#include <cassert>
#include <iomanip>

// contains definition of alt_bn128 ec public parameters
#include "libsnark/algebra/curves/alt_bn128/alt_bn128_pp.hpp"
// contains required interfaces and types (keypair, proof, generator, prover, verifier)
#include "libsnark/zk_proof_systems/ppzksnark/r1cs_ppzksnark/r1cs_ppzksnark.hpp"

using namespace std;
using namespace libsnark;

// conversion byte[32] <-> libsnark bigint.
libsnark::bigint<libsnark::alt_bn128_r_limbs> libsnarkBigintFromBytes(const uint8_t* _x)
{
  libsnark::bigint<libsnark::alt_bn128_r_limbs> x;

  for (unsigned i = 0; i < 4; i++) {
    for (unsigned j = 0; j < 8; j++) {
      x.data[3 - i] |= uint64_t(_x[i * 8 + j]) << (8 * (7-j));
    }
  }
  return x;
}

std::string HexStringFromLibsnarkBigint(libsnark::bigint<libsnark::alt_bn128_r_limbs> _x){
								uint8_t x[32];
								for (unsigned i = 0; i < 4; i++)
																for (unsigned j = 0; j < 8; j++)
																								x[i * 8 + j] = uint8_t(uint64_t(_x.data[3 - i]) >> (8 * (7 - j)));

								std::stringstream ss;
								ss << std::setfill('0');
								for (unsigned i = 0; i<32; i++) {
																ss << std::hex << std::setw(2) << (int)x[i];
								}

                std:string str = ss.str();
                return str.erase(0, min(str.find_first_not_of('0'), str.size()-1));
}

std::string outputPointG1AffineAsHex(libsnark::alt_bn128_G1 _p)
{
								libsnark::alt_bn128_G1 aff = _p;
								aff.to_affine_coordinates();
								return
																"0x" +
																HexStringFromLibsnarkBigint(aff.X.as_bigint()) +
																", 0x" +
																HexStringFromLibsnarkBigint(aff.Y.as_bigint()) +
																"";
}

std::string outputPointG2AffineAsHex(libsnark::alt_bn128_G2 _p)
{
								libsnark::alt_bn128_G2 aff = _p;
								aff.to_affine_coordinates();
								return
																"[0x" +
																HexStringFromLibsnarkBigint(aff.X.c1.as_bigint()) + ", 0x" +
																HexStringFromLibsnarkBigint(aff.X.c0.as_bigint()) + "], [0x" +
																HexStringFromLibsnarkBigint(aff.Y.c1.as_bigint()) + ", 0x" +
																HexStringFromLibsnarkBigint(aff.Y.c0.as_bigint()) + "]";
}

//takes input and puts it into constraint system
r1cs_ppzksnark_constraint_system<alt_bn128_pp> createConstraintSystem(const uint8_t* A, const uint8_t* B, const uint8_t* C, int constraints, int variables, int inputs)
{
  r1cs_constraint_system<Fr<alt_bn128_pp> > cs;
  cs.primary_input_size = inputs;
  cs.auxiliary_input_size = variables - inputs - 1; // ~one not included

  cout << "num variables: " << variables <<endl;
  cout << "num constraints: " << constraints <<endl;
  cout << "num inputs: " << inputs <<endl;

  for (int row = 0; row < constraints; row++) {
    linear_combination<Fr<alt_bn128_pp> > lin_comb_A, lin_comb_B, lin_comb_C;

    for (int idx=0; idx<variables; idx++) {
      libsnark::bigint<libsnark::alt_bn128_r_limbs> value = libsnarkBigintFromBytes(A+row*variables*32 + idx*32);
      // cout << "C entry " << idx << " in row " << row << ": " << value << endl;
      if (!value.is_zero()) {
        cout << "A(" << idx << ", " << value << ")" << endl;
        lin_comb_A.add_term(idx, value);
      }
    }
    for (int idx=0; idx<variables; idx++) {
      libsnark::bigint<libsnark::alt_bn128_r_limbs> value = libsnarkBigintFromBytes(B+row*variables*32 + idx*32);
      // cout << "B entry " << idx << " in row " << row << ": " << value << endl;
      if (!value.is_zero()) {
        cout << "B(" << idx << ", " << value << ")" << endl;
        lin_comb_B.add_term(idx, value);
      }
    }
    for (int idx=0; idx<variables; idx++) {
      libsnark::bigint<libsnark::alt_bn128_r_limbs> value = libsnarkBigintFromBytes(C+row*variables*32 + idx*32);
      // cout << "C entry " << idx << " in row " << row << ": " << value << endl;
      if (!value.is_zero()) {
        cout << "C(" << idx << ", " << value << ")" << endl;
        lin_comb_C.add_term(idx, value);
      }
    }
    cs.add_constraint(r1cs_constraint<Fr<alt_bn128_pp> >(lin_comb_A, lin_comb_B, lin_comb_C));
  }

  return cs;
}

// keypair generateKeypair(constraints)
r1cs_ppzksnark_keypair<alt_bn128_pp> generateKeypair(const r1cs_ppzksnark_constraint_system<alt_bn128_pp> &cs){
  // from r1cs_ppzksnark.hpp
  return r1cs_ppzksnark_generator<alt_bn128_pp>(cs);
}

template<typename T>
void writeToFile(std::string path, T& obj) {
    std::stringstream ss;
    ss << obj;
    std::ofstream fh;
    fh.open(path, std::ios::binary);
    ss.rdbuf()->pubseekpos(0, std::ios_base::out);
    fh << ss.rdbuf();
    fh.flush();
    fh.close();
}

template<typename T>
T loadFromFile(std::string path) {
    std::stringstream ss;
    std::ifstream fh(path, std::ios::binary);

    assert(fh.is_open());

    ss << fh.rdbuf();
    fh.close();

    ss.rdbuf()->pubseekpos(0, std::ios_base::in);

    T obj;
    ss >> obj;

    return obj;
}

void serializeProvingKeyToFile(r1cs_ppzksnark_proving_key<alt_bn128_pp> pk, const char* pk_path){
  writeToFile(pk_path, pk);
}

r1cs_ppzksnark_proving_key<alt_bn128_pp> deserializeProvingKeyFromFile(const char* pk_path){
  return loadFromFile<r1cs_ppzksnark_proving_key<alt_bn128_pp>>(pk_path);
}

void serializeVerificationKeyToFile(r1cs_ppzksnark_verification_key<alt_bn128_pp> vk, const char* vk_path){
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
void exportVerificationKey(r1cs_ppzksnark_keypair<alt_bn128_pp> keypair){
								unsigned icLength = keypair.vk.encoded_IC_query.rest.indices.size() + 1;

								cout << "\tVerification key in Solidity compliant format:{" << endl;
								cout << "\t\tvk.A = Pairing.G2Point(" << outputPointG2AffineAsHex(keypair.vk.alphaA_g2) << ");" << endl;
								cout << "\t\tvk.B = Pairing.G1Point(" << outputPointG1AffineAsHex(keypair.vk.alphaB_g1) << ");" << endl;
								cout << "\t\tvk.C = Pairing.G2Point(" << outputPointG2AffineAsHex(keypair.vk.alphaC_g2) << ");" << endl;
								cout << "\t\tvk.gamma = Pairing.G2Point(" << outputPointG2AffineAsHex(keypair.vk.gamma_g2) << ");" << endl;
								cout << "\t\tvk.gammaBeta1 = Pairing.G1Point(" << outputPointG1AffineAsHex(keypair.vk.gamma_beta_g1) << ");" << endl;
								cout << "\t\tvk.gammaBeta2 = Pairing.G2Point(" << outputPointG2AffineAsHex(keypair.vk.gamma_beta_g2) << ");" << endl;
								cout << "\t\tvk.Z = Pairing.G2Point(" << outputPointG2AffineAsHex(keypair.vk.rC_Z_g2) << ");" << endl;
								cout << "\t\tvk.IC = new Pairing.G1Point[](" << icLength << ");" << endl;
								cout << "\t\tvk.IC[0] = Pairing.G1Point(" << outputPointG1AffineAsHex(keypair.vk.encoded_IC_query.first) << ");" << endl;
								for (size_t i = 1; i < icLength; ++i)
								{
																auto vkICi = outputPointG1AffineAsHex(keypair.vk.encoded_IC_query.rest.values[i - 1]);
																cout << "\t\tvk.IC[" << i << "] = Pairing.G1Point(" << vkICi << ");" << endl;
								}
								cout << "\t\t}" << endl;

}

// compliant with solidty verification example
void exportInput(r1cs_primary_input<Fr<alt_bn128_pp>> input){
								cout << "\tInput in Solidity compliant format:{" << endl;
								for (size_t i = 0; i < input.size(); ++i)
								{
																cout << "\t\tinput[" << i << "] = " << HexStringFromLibsnarkBigint(input[i].as_bigint()) << ";" << endl;
								}
								cout << "\t\t}" << endl;
}

// compliant with solidty verification example
void exportProof(r1cs_ppzksnark_proof<alt_bn128_pp> proof){
                cout << "\tstruct Proof {\n"
                   "\t\tPairing.G1Point A;\n"
                   "\t\tPairing.G1Point A_p;\n"
                   "\t\tPairing.G2Point B;\n"
                   "\t\tPairing.G1Point B_p;\n"
                   "\t\tPairing.G1Point C;\n"
                   "\t\tPairing.G1Point C_p;\n"
                   "\t\tPairing.G1Point K;\n"
                   "\t\tPairing.G1Point H;\n"
                 "\t}" << endl;

                cout << "\t//Proof in Solidity compliant format:{" << endl;
                cout << "\t\tproof.A = Pairing.G1Point(" << outputPointG1AffineAsHex(proof.g_A.g) << ");" << endl;
                cout << "\t\tproof.A_p = Pairing.G1Point(" << outputPointG1AffineAsHex(proof.g_A.h) << ");" << endl;
                cout << "\t\tproof.B = Pairing.G2Point(" << outputPointG2AffineAsHex(proof.g_B.g) << ");" << endl;
                cout << "\t\tproof.B_p = Pairing.G1Point(" << outputPointG1AffineAsHex(proof.g_B.h) << ");" << endl;
                cout << "\t\tproof.C = Pairing.G1Point(" << outputPointG1AffineAsHex(proof.g_C.g) << ");" << endl;
                cout << "\t\tproof.C_p = Pairing.G1Point(" << outputPointG1AffineAsHex(proof.g_C.h) << ");" << endl;
                cout << "\t\tproof.H = Pairing.G1Point(" << outputPointG1AffineAsHex(proof.g_H) << ");" << endl;
                cout << "\t\tproof.K = Pairing.G1Point(" << outputPointG1AffineAsHex(proof.g_K) << ");" << endl;
                cout << "\t}" << endl;

}

bool _setup(const uint8_t* A, const uint8_t* B, const uint8_t* C, int constraints, int variables, int inputs, const char* pk_path, const char* vk_path)
{
  libsnark::inhibit_profiling_info = true;
  libsnark::inhibit_profiling_counters = true;

  //initialize curve parameters
  alt_bn128_pp::init_public_params();

  r1cs_constraint_system<Fr<alt_bn128_pp>> cs;
  cs = createConstraintSystem(A, B ,C , constraints, variables, inputs);

  assert(cs.num_variables() >= inputs);
  assert(cs.num_inputs() == inputs);
  assert(cs.num_constraints() == constraints);

  // create keypair
  r1cs_ppzksnark_keypair<alt_bn128_pp> keypair = r1cs_ppzksnark_generator<alt_bn128_pp>(cs);

  // Export vk and pk to files
  serializeProvingKeyToFile(keypair.pk, pk_path);
  serializeVerificationKeyToFile(keypair.vk, vk_path);

  // Print VerificationKey in Solidity compatible format
  exportVerificationKey(keypair);

  return true;
}

bool _generate_proof(const char* pk_path, const uint8_t* public_inputs, int public_inputs_length, const uint8_t* private_inputs, int private_inputs_length)
{
  libsnark::inhibit_profiling_info = true;
  libsnark::inhibit_profiling_counters = true;

  //initialize curve parameters
  alt_bn128_pp::init_public_params();
  r1cs_ppzksnark_proving_key<alt_bn128_pp> pk = deserializeProvingKeyFromFile(pk_path);

  // assign variables based on witness values, excludes ~one
  r1cs_variable_assignment<Fr<alt_bn128_pp> > full_variable_assignment;
  for (int i = 1; i < public_inputs_length; i++) {
    full_variable_assignment.push_back(Fr<alt_bn128_pp>(libsnarkBigintFromBytes(public_inputs + i*32)));
  }
  for (int i = 0; i < private_inputs_length; i++) {
    full_variable_assignment.push_back(Fr<alt_bn128_pp>(libsnarkBigintFromBytes(private_inputs + i*32)));
  }

  // split up variables into primary and auxiliary inputs. Does *NOT* include the constant 1 */
  // Public variables belong to primary input, private variables are auxiliary input.
  r1cs_primary_input<Fr<alt_bn128_pp>> primary_input(full_variable_assignment.begin(), full_variable_assignment.begin() + public_inputs_length-1);
  r1cs_primary_input<Fr<alt_bn128_pp>> auxiliary_input(full_variable_assignment.begin() + public_inputs_length-1, full_variable_assignment.end());
  // for debugging
  cout << "full variable assignment:"<< endl << full_variable_assignment;
  cout << "primary input:"<< endl << primary_input;
  cout << "auxiliary input:"<< endl << auxiliary_input;

  // Proof Generation
  r1cs_ppzksnark_proof<alt_bn128_pp> proof = r1cs_ppzksnark_prover<alt_bn128_pp>(pk, primary_input, auxiliary_input);

  // print proof
  exportProof(proof);

  return true;
}


bool _run_libsnark(const uint8_t* A, const uint8_t* B, const uint8_t* C, const uint8_t* witness, int constraints, int variables, int inputs)
{

  libsnark::inhibit_profiling_info = true;
  libsnark::inhibit_profiling_counters = true;

  //initialize curve parameters
  alt_bn128_pp::init_public_params();

  // for testing of serialization only. remove later.
  // string decString = "123456789123456789123456789";
  // string hexString = "0x661efdf2e3b19f7c045f15";
  // libsnark::bigint<libsnark::alt_bn128_r_limbs> value = bigint<libsnark::alt_bn128_r_limbs>(decString.c_str());
  //
  // cout << "expected: " << hexString << endl;
  // cout << "computed: " << "0x"+HexStringFromLibsnarkBigint(value) <<endl;
  // assert("0x"+HexStringFromLibsnarkBigint(value) == hexString);

  // Setup:
  // create constraint system
  r1cs_constraint_system<Fr<alt_bn128_pp>> cs;
  cs = createConstraintSystem(A, B ,C , constraints, variables, inputs);

  // assign variables based on witness values, excludes ~one
  r1cs_variable_assignment<Fr<alt_bn128_pp> > full_variable_assignment;
  for (int i = 1; i < variables; i++) {
    // for debugging
    cout << "witness_hex ["<< i << "]: " << HexStringFromLibsnarkBigint(libsnarkBigintFromBytes(witness + i*32)) << endl;
    cout << "fieldElement ["<< i << "]: " << HexStringFromLibsnarkBigint((Fr<alt_bn128_pp>(libsnarkBigintFromBytes(witness + i*32))).as_bigint()) << endl;
    full_variable_assignment.push_back(Fr<alt_bn128_pp>(libsnarkBigintFromBytes(witness + i*32)));
  }

  // split up variables into primary and auxiliary inputs. Does *NOT* include the constant 1 */
  // Output variables belong to primary input, helper variables are auxiliary input.
  // TODO: At the moment, this has implicit assumptions regarding ordering.
  // The inputs to the run_libsnark_functions need to put primary inputs first.
  r1cs_primary_input<Fr<alt_bn128_pp>> primary_input(full_variable_assignment.begin(), full_variable_assignment.begin() + inputs);
  r1cs_primary_input<Fr<alt_bn128_pp>> auxiliary_input(full_variable_assignment.begin() + inputs, full_variable_assignment.end());

  // for debugging
  cout << "full variable assignment :"<< endl << full_variable_assignment;

  // sanity checks
  assert(cs.num_variables() == full_variable_assignment.size());
  assert(cs.num_variables() >= inputs);
  assert(cs.num_inputs() == inputs);
  assert(cs.num_constraints() == constraints);
  assert(cs.is_satisfied(primary_input, auxiliary_input));

  // create keypair
  r1cs_ppzksnark_keypair<alt_bn128_pp> keypair = r1cs_ppzksnark_generator<alt_bn128_pp>(cs);

	// Print VerificationKey in Solidity compatible format
	exportVerificationKey(keypair);

  // print primary input
  exportInput(primary_input);

  // Proof Generation
  r1cs_ppzksnark_proof<alt_bn128_pp> proof = r1cs_ppzksnark_prover<alt_bn128_pp>(keypair.pk, primary_input, auxiliary_input);

  // print proof
  exportProof(proof);

  // Verification
  bool result = r1cs_ppzksnark_verifier_strong_IC<alt_bn128_pp>(keypair.vk, primary_input, proof);

  return result;
}
