/**
 * @file wraplibsnark.cpp
 * @author Dennis Kuhnert <dennis.kuhnert@campus.tu-berlin.de>
 * @author Jacob Eberhardt <jacob.eberhardt@tu-berlin.de
 * @date 2017
 */

#include "wraplibsnark.hpp"
#include <iostream>
#include <cassert>
#include <iomanip>

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
// libsnark/relations/constraint_satisfaction_problems/r1cs/r1cs.hpp

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

								return ss.str();
}

std::string outputPointG1Affine(libsnark::alt_bn128_G1 _p)
{
								libsnark::alt_bn128_G1 aff = _p;
								aff.to_affine_coordinates();
								return
																"Pairing.g1FromAffine(0x" +
																HexStringFromLibsnarkBigint(aff.X.as_bigint()) +
																", 0x" +
																HexStringFromLibsnarkBigint(aff.Y.as_bigint()) +
																")";
}

std::string outputPointG2Affine(libsnark::alt_bn128_G2 _p)
{
								libsnark::alt_bn128_G2 aff = _p;
								aff.to_affine_coordinates();
								return
																"Pairing.g2FromAffine([0x" +
																HexStringFromLibsnarkBigint(aff.X.c1.as_bigint()) + ", 0x" +
																HexStringFromLibsnarkBigint(aff.X.c0.as_bigint()) + "], [0x" +
																HexStringFromLibsnarkBigint(aff.Y.c1.as_bigint()) + ", 0x" +
																HexStringFromLibsnarkBigint(aff.Y.c0.as_bigint()) + "])";
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

// compliant with solidty, from c++ client libsnark integration
void exportVerificationKey(r1cs_ppzksnark_keypair<alt_bn128_pp> keypair){
								unsigned icLength = keypair.vk.encoded_IC_query.rest.indices.size() + 1;

								cout << "\tVerification key in Solidity compliant format:{" << endl;
								cout << "\t\tvk.A = " << outputPointG2Affine(keypair.vk.alphaA_g2) << ";" << endl;
								cout << "\t\tvk.B = " << outputPointG1Affine(keypair.vk.alphaB_g1) << ";" << endl;
								cout << "\t\tvk.C = " << outputPointG2Affine(keypair.vk.alphaC_g2) << ";" << endl;
								cout << "\t\tvk.gamma = " << outputPointG2Affine(keypair.vk.gamma_g2) << ";" << endl;
								cout << "\t\tvk.gammaBeta1 = " << outputPointG1Affine(keypair.vk.gamma_beta_g1) << ";" << endl;
								cout << "\t\tvk.gammaBeta2 = " << outputPointG2Affine(keypair.vk.gamma_beta_g2) << ";" << endl;
								cout << "\t\tvk.Z = " << outputPointG2Affine(keypair.vk.rC_Z_g2) << ";" << endl;
								cout << "\t\tvk.IC = new Pairing.G1Point[](" << icLength << ");" << endl;
								cout << "\t\tvk.IC[0] = " << outputPointG1Affine(keypair.vk.encoded_IC_query.first) << ";" << endl;
								for (size_t i = 1; i < icLength; ++i)
								{
																auto vkICi = outputPointG1Affine(keypair.vk.encoded_IC_query.rest.values[i - 1]);
																cout << "\t\tvk.IC[" << i << "] = " << vkICi << ";" << endl;
								}
								cout << "\t\t}" << endl;

}

// compliant with solidty verification example
void exportProof(r1cs_ppzksnark_proof<alt_bn128_pp> proof){
                // solidity data structure
                // struct Proof {
                //   Pairing.G1Point A;
                //   Pairing.G1Point A_p;
                //   Pairing.G2Point B;
                //   Pairing.G1Point B_p;
                //   Pairing.G1Point C;
                //   Pairing.G1Point C_p;
                //   Pairing.G1Point K;
                //   Pairing.G1Point H;
                // }
                cout << "\Proof in Solidity compliant format:{" << endl;
                cout << "proof.g_A.g: " << outputPointG1Affine(proof.g_A.g) << ";" << endl;
                cout << "proof.g_A.h: " << outputPointG1Affine(proof.g_A.h) << ";" << endl;
                cout << "proof.g_B.g: " << outputPointG2Affine(proof.g_B.g) << ";" << endl;
                cout << "proof.g_B.h: " << outputPointG1Affine(proof.g_B.h) << ";" << endl;
                cout << "proof.g_C.g: " << outputPointG1Affine(proof.g_C.g) << ";" << endl;
                cout << "proof.g_C.h: " << outputPointG1Affine(proof.g_C.h) << ";" << endl;
                cout << "proof.g_H: " << outputPointG1Affine(proof.g_H) << ";" << endl;
                cout << "proof.g_K: " << outputPointG1Affine(proof.g_K) << ";" << endl;
                cout << "\t\t}" << endl;

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

  //split up variables into primary and auxiliary inputs
  // TODO: Check whether this is consistent with inputs from VerifiableStatementCompiler
  r1cs_primary_input<Fr<alt_bn128_pp> > primary_input(full_variable_assignment.begin(), full_variable_assignment.begin() + variables - 1);
  r1cs_primary_input<Fr<alt_bn128_pp> > auxiliary_input(full_variable_assignment.begin() + variables - 1, full_variable_assignment.end());

  // sanity checks
  assert(cs.num_variables() == full_variable_assignment.size());
  assert(cs.num_variables() >= variables - 1);
  assert(cs.num_inputs() == variables - 1);
  assert(cs.num_constraints() == constraints);
  assert(cs.is_satisfied(primary_input, auxiliary_input));

  //initialize curve parameters
  alt_bn128_pp::init_public_params();

  // create keypair
  r1cs_ppzksnark_keypair<alt_bn128_pp> keypair = r1cs_ppzksnark_generator<alt_bn128_pp>(cs);

	// Print VerificationKey in Solidity compatible format
	exportVerificationKey(keypair);


  // Proof Generation
  r1cs_ppzksnark_proof<alt_bn128_pp> proof = r1cs_ppzksnark_prover<alt_bn128_pp>(keypair.pk, primary_input, auxiliary_input);

  // proof.A = Pairing.G1Point(12873740738727497448187997291915224677121726020054032516825496230827252793177, 21804419174137094775122804775419507726154084057848719988004616848382402162497);
	// 		proof.A_p = Pairing.G1Point(7742452358972543465462254569134860944739929848367563713587808717088650354556, 7324522103398787664095385319014038380128814213034709026832529060148225837366);
	// 		proof.B = Pairing.G2Point(
	// 			[8176651290984905087450403379100573157708110416512446269839297438960217797614, 15588556568726919713003060429893850972163943674590384915350025440408631945055],
	// 			[15347511022514187557142999444367533883366476794364262773195059233657571533367, 4265071979090628150845437155927259896060451682253086069461962693761322642015]);
	// 		proof.B_p = Pairing.G1Point(2979746655438963305714517285593753729335852012083057917022078236006592638393, 6470627481646078059765266161088786576504622012540639992486470834383274712950);
	// 		proof.C = Pairing.G1Point(6851077925310461602867742977619883934042581405263014789956638244065803308498, 10336382210592135525880811046708757754106524561907815205241508542912494488506);
	// 		proof.C_p = Pairing.G1Point(12491625890066296859584468664467427202390981822868257437245835716136010795448, 13818492518017455361318553880921248537817650587494176379915981090396574171686);
	// 		proof.H = Pairing.G1Point(12091046215835229523641173286701717671667447745509192321596954139357866668225, 14446807589950902476683545679847436767890904443411534435294953056557941441758);
	// 		proof.K = Pairing.G1Point(21341087976609916409401737322664290631992568431163400450267978471171152600502, 2942165230690572858696920423896381470344658299915828986338281196715687693170);


  // print proof
  exportProof(proof);

  // Verification
  bool result = r1cs_ppzksnark_verifier_strong_IC<alt_bn128_pp>(keypair.vk, primary_input, proof);

  return result;
}
