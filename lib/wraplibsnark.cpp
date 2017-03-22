/**
 * @file wraplibsnark.cpp
 * @author Dennis Kuhnert <dennis.kuhnert@campus.tu-berlin.de>
 * @date 2017
 */

#include "wraplibsnark.hpp"
#include <iostream>
#include <cassert>

// contains definition of alt_bn128 ec public parameters
#include "libsnark/algebra/curves/alt_bn128/alt_bn128_pp.hpp"

// contains required interfaces and types (keypair, proof, generator, prover, verifier)
#include "libsnark/zk_proof_systems/ppzksnark/r1cs_ppzksnark/r1cs_ppzksnark.hpp"

// contains usage example for these interfaces
//#include "libsnark/zk_proof_systems/ppzksnark/r1cs_ppzksnark/examples/run_r1cs_ppzksnark.hpp"

// How to "zkSNARK from R1CS:"
// libsnark/relations/constraint_satisfaction_problems/r1cs/examples/r1cs_examples.tcc

// How to generate R1CS Example
// libsnark/zk_proof_systems/ppzksnark/r1cs_ppzksnark/examples/run_r1cs_ppzksnark.tcc

// Interfaces for R1CS
// libsnark /relations/constraint_satisfaction_problems/r1cs/r1cs.hpp

using namespace std;
using namespace libsnark;

// conversion byte[32] <-> libsnark bigint.
libsnark::bigint<libsnark::alt_bn128_r_limbs> libsnarkBigintFromBytes(const uint8_t* _x)
{
								libsnark::bigint<libsnark::alt_bn128_r_limbs> x;

								for (unsigned i = 0; i < 4; i++)
																for (unsigned j = 0; j < 8; j++)
																								x.data[3 - i] |= uint64_t(_x[i * 8 + j]) << (8 * (7-j));
								return x;
}

//takes input and puts it into constraint system
r1cs_ppzksnark_constraint_system<alt_bn128_pp> createConstraintSystem(const uint8_t* A, const uint8_t* B, const uint8_t* C, const uint8_t* witness, int constraints, int variables)
{
								r1cs_constraint_system<Fr<alt_bn128_pp> > cs;
								cs.primary_input_size = variables - 1;
								cs.auxiliary_input_size = 0;

								cout << "num variables: " << variables <<endl;
								cout << "num constraints: " << constraints <<endl;

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
								for (int idx=0; idx<variables; idx++) {
																cout << "witness entry " << idx << ": " << libsnarkBigintFromBytes(witness + idx*32) << endl;
								}

								return cs;
}

// keypair generateKeypair(constraints)
r1cs_ppzksnark_keypair<alt_bn128_pp> generateKeypair(const r1cs_ppzksnark_constraint_system<alt_bn128_pp> &cs){
								// from r1cs_ppzksnark.hpp
								return r1cs_ppzksnark_generator<alt_bn128_pp>(cs);
}

// TODO: Check with solidity format. Also, is IC_Query needed?
void printVerificationKey(r1cs_ppzksnark_keypair<alt_bn128_pp> keypair){
								printf("Verification key:\n");
								printf("vk.alphaA_g2: "); keypair.vk.alphaA_g2.print();
								printf("\nvk.alphaB_g1: "); keypair.vk.alphaB_g1.print();
								printf("\nvk.alphaC_g2: "); keypair.vk.alphaC_g2.print();
								printf("\nvk.gamma_g2: "); keypair.vk.gamma_g2.print();
								printf("\nvk.gamma_beta_g1: "); keypair.vk.gamma_beta_g1.print();
								printf("\nvk.gamma_beta_g2: "); keypair.vk.gamma_beta_g2.print();
								printf("\nvk.rC_Z_g2: "); keypair.vk.rC_Z_g2.print();
								//printf("\nvk.encoded_IC_query: "); keypair.vk.encoded_IC_query.print();
}


bool _run_libsnark(const uint8_t* A, const uint8_t* B, const uint8_t* C, const uint8_t* witness, int constraints, int variables)
{
								// Setup:
								// create constraint system
								r1cs_constraint_system<Fr<alt_bn128_pp> > cs;
								cs = createConstraintSystem(A,B,C,witness,constraints,variables);

								// assign variables
								r1cs_variable_assignment<Fr<alt_bn128_pp> > full_variable_assignment;
								for (int i = 1; i < variables; i++) {
																full_variable_assignment.push_back(witness[i]);
								}

								// //split up variables into primary and auxiliary inputs
								// // TODO: Check whether this is consistent with inputs from VerifiableStatementCompiler
								// r1cs_primary_input<Fr<alt_bn128_pp> > primary_input(full_variable_assignment.begin(), full_variable_assignment.begin() + variables - 1);
								// r1cs_primary_input<Fr<alt_bn128_pp> > auxiliary_input(full_variable_assignment.begin() + variables - 1, full_variable_assignment.end());
								//
								// // sanity checks
								// assert(cs.num_variables() == full_variable_assignment.size());
								// assert(cs.num_variables() >= variables - 1);
								// assert(cs.num_inputs() == variables - 1);
								// assert(cs.num_constraints() == constraints);
								// assert(cs.is_satisfied(primary_input, auxiliary_input));
								//
								// //initialize curve parameters
								// alt_bn128_pp::init_public_params();
								//
								// // create keypair
								// r1cs_ppzksnark_keypair<alt_bn128_pp> keypair = r1cs_ppzksnark_generator<alt_bn128_pp>(cs);
								//
								// // Print VerificationKey
								// printVerificationKey(keypair);
								//
								// // Proof Generation
								// r1cs_ppzksnark_proof<alt_bn128_pp> proof = r1cs_ppzksnark_prover<alt_bn128_pp>(keypair.pk, primary_input, auxiliary_input);
								//
								// // Verification
								// bool result = r1cs_ppzksnark_verifier_strong_IC<alt_bn128_pp>(keypair.vk, primary_input, proof);
								//
								// return result;
								return true;
}
