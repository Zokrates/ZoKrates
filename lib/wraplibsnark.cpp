/**
 * @file wraplibsnark.cpp
 * @author Dennis Kuhnert <dennis.kuhnert@campus.tu-berlin.de>
 * @date 2017
 */

#include "wraplibsnark.hpp"
#include <iostream>
#include <cassert>

#include "libsnark/common/default_types/r1cs_ppzksnark_pp.hpp"
#include "libsnark/zk_proof_systems/ppzksnark/r1cs_ppzksnark/examples/run_r1cs_ppzksnark.hpp"

using namespace std;
using namespace libsnark;

bool _run_libsnark(const int* A, const int* B, const int* C, const int* witness, int constraints, int variables){
  r1cs_constraint_system<Fr<default_r1cs_ppzksnark_pp> > cs;
  cs.primary_input_size = variables - 1;
  cs.auxiliary_input_size = 0;

  cout << endl << "run_libsnark" << endl;
  for (int row = 0; row < constraints; row++) {
    // cout << "row " << row << endl;
    linear_combination<Fr<default_r1cs_ppzksnark_pp> > lin_comb_A, lin_comb_B, lin_comb_C;
    for (int idx = 0; idx < variables; idx++) {
      // using (constraints + 2) because of the representation of Rust's Vec<_>
      if (A[row * (constraints + 2) + idx] != 0) {
        // cout << "A(" << idx << ", " << A[row * (constraints + 2) + idx] << ")" << endl;
        lin_comb_A.add_term(idx, A[row * (constraints + 2) + idx]);
      }
      if (B[row * (constraints + 2) + idx] != 0) {
        // cout << "B(" << idx << ", " << B[row * (constraints + 2) + idx] << ")" << endl;
        lin_comb_B.add_term(idx, B[row * (constraints + 2) + idx]);
      }
      if (C[row * (constraints + 2) + idx] != 0) {
        // cout << "C(" << idx << ", " << C[row * (constraints + 2) + idx] << ")" << endl;
        lin_comb_C.add_term(idx, C[row * (constraints + 2) + idx]);
      }
    }
    cs.add_constraint(r1cs_constraint<Fr<default_r1cs_ppzksnark_pp> >(lin_comb_A, lin_comb_B, lin_comb_C));
  }

  r1cs_variable_assignment<Fr<default_r1cs_ppzksnark_pp> > full_variable_assignment;
  for (int i = 1; i < variables; i++) {
    full_variable_assignment.push_back(witness[i]);
  }

  r1cs_primary_input<Fr<default_r1cs_ppzksnark_pp> > primary_input(full_variable_assignment.begin(), full_variable_assignment.begin() + variables - 1);
  r1cs_primary_input<Fr<default_r1cs_ppzksnark_pp> > auxiliary_input(full_variable_assignment.begin() + variables - 1, full_variable_assignment.end());

  /* sanity checks */
  assert(cs.num_variables() == full_variable_assignment.size());
  assert(cs.num_variables() >= variables - 1);
  assert(cs.num_inputs() == variables - 1);
  assert(cs.num_constraints() == constraints);
  assert(cs.is_satisfied(primary_input, auxiliary_input));
  r1cs_example<Fr<default_r1cs_ppzksnark_pp> > example = r1cs_example<Fr<default_r1cs_ppzksnark_pp> >(std::move(cs), std::move(primary_input), std::move(auxiliary_input));

  print_header("(enter) Profile R1CS ppzkSNARK");
  default_r1cs_ppzksnark_pp::init_public_params();
  const bool test_serialization = true;
  bool result = run_r1cs_ppzksnark<default_r1cs_ppzksnark_pp>(example, test_serialization);
  print_header("(leave) Profile R1CS ppzkSNARK");

  return result;
}
