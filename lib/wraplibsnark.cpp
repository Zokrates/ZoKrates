/**
 * @file wraplibsnark.cpp
 * @author Dennis Kuhnert <dennis.kuhnert@campus.tu-berlin.de>
 * @date 2017
 */

#include "wraplibsnark.hpp"
#include <iostream>
#include <cassert>

//#include "connector.hpp"

//should be removed later
#include "libsnark/common/default_types/r1cs_ppzksnark_pp.hpp"
#include "libsnark/zk_proof_systems/ppzksnark/r1cs_ppzksnark/examples/run_r1cs_ppzksnark.hpp"

using namespace std;
using namespace libsnark;

// conversion byte[32] bigend <-> libsnark bigint (internally 64bit[4] littleend).
libsnark::bigint<libsnark::alt_bn128_r_limbs> libsnarkBigintFromBytes(const uint8_t* _x)
{
	libsnark::bigint<libsnark::alt_bn128_r_limbs> x;

	for (unsigned i = 0; i < 4; i++)
		for (unsigned j = 0; j < 8; j++)

      x.data[3 - i] |= uint64_t(_x[i * 8 + j]) << (8 * (7-j));
	return x;
}

bool _run_libsnark(const uint8_t* A, const uint8_t* B, const uint8_t* C, const uint8_t* witness, int constraints, int variables){
  r1cs_constraint_system<Fr<default_r1cs_ppzksnark_pp> > cs;
  cs.primary_input_size = variables - 1;
  cs.auxiliary_input_size = 0;

cout << "num variables: " << variables <<endl;
cout << "num constraints: " << constraints <<endl;

for (int row = 0; row < constraints; row++) {
  linear_combination<Fr<default_r1cs_ppzksnark_pp> > lin_comb_A, lin_comb_B, lin_comb_C;

  for (int idx=0; idx<variables; idx++){
    cout << "A entry " << idx << " in row " << row << ": " << libsnarkBigintFromBytes(A+row*constraints*32 + idx*32) << endl;
  }
  for (int idx=0; idx<variables; idx++){
    cout << "B entry " << idx << " in row " << row << ": " << libsnarkBigintFromBytes(B+row*constraints*32 + idx*32) << endl;
  }
  for (int idx=0; idx<variables; idx++){
    cout << "C entry " << idx << " in row " << row << ": " << libsnarkBigintFromBytes(C+row*constraints*32 + idx*32) << endl;
  }
}

for (int idx=0; idx<variables; idx++){
  cout << "witness entry " << idx << ": " << libsnarkBigintFromBytes(witness + idx*32) << endl;
}

  //
  // cout << endl << "run_libsnark" << endl;
  // for (int row = 0; row < constraints; row++) {
  //   cout << "row " << row << endl;
  //   linear_combination<Fr<default_r1cs_ppzksnark_pp> > lin_comb_A, lin_comb_B, lin_comb_C;
  //   for (int idx = 0; idx < variables; idx++) {
  //     // using (constraints + 2) because of the representation of Rust's Vec<_>
  //     if (A[row * (constraints + 2) + idx] != 0) {
  //       cout << "A(" << idx << ", " << libsnarkBigintFromBytes(A[row * (constraints + 2) + idx]) << ")" << endl;
  //       lin_comb_A.add_term(idx, A[row * (constraints + 2) + idx]);
  //     }
  //     if (B[row * (constraints + 2) + idx] != 0) {
  //       cout << "B(" << idx << ", " << B[row * (constraints + 2) + idx] << ")" << endl;
  //       lin_comb_B.add_term(idx, B[row * (constraints + 2) + idx]);
  //     }
  //     if (C[row * (constraints + 2) + idx] != 0) {
  //       cout << "C(" << idx << ", " << C[row * (constraints + 2) + idx] << ")" << endl;
  //       lin_comb_C.add_term(idx, C[row * (constraints + 2) + idx]);
  //     }
  //   }
  //   cs.add_constraint(r1cs_constraint<Fr<default_r1cs_ppzksnark_pp> >(lin_comb_A, lin_comb_B, lin_comb_C));
  // }

  // r1cs_variable_assignment<Fr<default_r1cs_ppzksnark_pp> > full_variable_assignment;
  // for (int i = 1; i < variables; i++) {
  //   full_variable_assignment.push_back(witness[i]);
  // }
  //
  // r1cs_primary_input<Fr<default_r1cs_ppzksnark_pp> > primary_input(full_variable_assignment.begin(), full_variable_assignment.begin() + variables - 1);
  // r1cs_primary_input<Fr<default_r1cs_ppzksnark_pp> > auxiliary_input(full_variable_assignment.begin() + variables - 1, full_variable_assignment.end());
  //
  // /* sanity checks */
  // assert(cs.num_variables() == full_variable_assignment.size());
  // assert(cs.num_variables() >= variables - 1);
  // assert(cs.num_inputs() == variables - 1);
  // assert(cs.num_constraints() == constraints);
  // assert(cs.is_satisfied(primary_input, auxiliary_input));
  // r1cs_example<Fr<default_r1cs_ppzksnark_pp> > example = r1cs_example<Fr<default_r1cs_ppzksnark_pp> >(std::move(cs), std::move(primary_input), std::move(auxiliary_input));
  //
  // print_header("(enter) Profile R1CS ppzkSNARK");
  // default_r1cs_ppzksnark_pp::init_public_params();
  // const bool test_serialization = true;
  // bool result = run_r1cs_ppzksnark<default_r1cs_ppzksnark_pp>(example, test_serialization);
  // print_header("(leave) Profile R1CS ppzkSNARK");

  // return result;
  return true;
}
