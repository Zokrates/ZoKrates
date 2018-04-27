//https://gist.github.com/kobigurk/24c25e68219df87c348f1a78db51bb52

#include <iostream>

//#include "wraplibsnarkgadgets.cpp"

/*#include "libsnark/gadgetlib1/gadget.hpp"
#include "libsnark/gadgetlib1/protoboard.hpp"
#include "libff/common/default_types/ec_pp.hpp"
#include "libsnark/reductions/r1cs_to_qap/r1cs_to_qap.hpp"

#include <libsnark/common/data_structures/merkle_tree.hpp>
#include <libsnark/gadgetlib1/gadgets/basic_gadgets.hpp>
#include <libsnark/gadgetlib1/gadgets/hashes/hash_io.hpp>
#include <libsnark/gadgetlib1/gadgets/hashes/sha256/sha256_components.hpp>
#include <libsnark/gadgetlib1/gadgets/hashes/sha256/sha256_gadget.hpp>*/
#include "./sha256_ethereum.cpp"

//r1cs to json
#include <libsnark/zk_proof_systems/ppzksnark/r1cs_ppzksnark/r1cs_ppzksnark.hpp>


using namespace libsnark;
using namespace libff;

using std::vector;


template<typename FieldT>
std::string r1cs_to_json(protoboard<FieldT> pb, uint input_variables)
    {  
    // output inputs, right now need to compile with debug flag so that the `variable_annotations`
    // exists. Having trouble setting that up so will leave for now.
    r1cs_constraint_system<FieldT> constraints = pb.get_constraint_system();
    std::stringstream ss;
    ss << "\n{\"variables\":[";

    for (size_t i = 0; i < input_variables + 1; ++i)
    {   
        ss << '"' << constraints.variable_annotations[i].c_str() << '"';
        if (i < input_variables ) {
            ss << ", ";
        }
    }
    ss << "],\n";
    ss << "\"constraints\":[";
     
    for (size_t c = 0; c < constraints.num_constraints(); ++c)
    {   
        ss << "[";// << "\"A\"=";
        constraint_to_json(constraints.constraints[c].a, ss);
        ss << ",";// << "\"B\"=";
        constraint_to_json(constraints.constraints[c].b, ss);
        ss << ",";// << "\"A\"=";;
        constraint_to_json(constraints.constraints[c].c, ss);
        if (c == constraints.num_constraints()-1 ) {
            ss << "]\n";
        } else {
            ss << "],\n";
        }
    } 
    ss << "]}";
    ss.rdbuf()->pubseekpos(0, std::ios_base::out);  
    return ss.str(); 
}

template<typename FieldT>
std::string _sha256Constraints() {

    protoboard<FieldT> pb;
    std::shared_ptr<sha256_ethereum> hash;

    block_variable<FieldT> input;
    block_variable<FieldT> output;
    hash.reset(new sha256_ethereum(
        pb, 256, input, output, "cm_hash"
    ));
    hash->generate_r1cs_constraints(true);

    return(r1cs_to_json(pb, 10));
}

template <typename FieldT>
std::string array_to_json(protoboard<FieldT> pb)
{

    std::stringstream ss;
    r1cs_variable_assignment<FieldT> values = pb.full_variable_assignment();
    ss << "\n{\"TestVariables\":[";

    for (size_t i = 0; i < values.size(); ++i)
    {

        ss << values[i].as_bigint();
        if (i <  values.size() - 1) { ss << ",";}
    }

    ss << "]}\n";
    ss.rdbuf()->pubseekpos(0, std::ios_base::out);

    return(ss.str());
}



template<typename FieldT>
std::string _sha256Witness( pb_variable_array<FieldT> left, pb_variable_array<FieldT> right)
{

    protoboard<FieldT> pb;
    std::shared_ptr<sha256_ethereum> hash;

    pb_variable<FieldT> ZERO;
    ZERO.allocate(pb, "ZERO");
    pb.val(ZERO) = 0;

    pb.set_input_sizes(90);

    block_variable<FieldT> output;
    block_variable<FieldT> input =  block_variable<FieldT>(pb, {
        from_bits(left, ZERO),
        from_bits(right, ZERO)
    }, "input_variable");


    hash.reset(new sha256_ethereum(
        pb, 256, input, output, "cm_hash"
    ));

    hash->generate_r1cs_constraints(true);
    hash->generate_r1cs_witness();




    return(array_to_json(hash->pb));

}

