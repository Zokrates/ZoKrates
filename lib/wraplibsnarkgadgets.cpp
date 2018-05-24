//https://gist.github.com/kobigurk/24c25e68219df87c348f1a78db51bb52

#include "wraplibsnarkgadgets.hpp"
#include "sha256_ethereum.hpp"

#include <libsnark/zk_proof_systems/ppzksnark/r1cs_ppzksnark/r1cs_ppzksnark.hpp>


#include <iostream>

using namespace libsnark;
using namespace libff;

void constraint_to_json(linear_combination<FieldT> constraints, std::stringstream &ss)
{
    ss << "{";
    uint count = 0;
    for (const linear_term<FieldT>& lt : constraints.terms)
    {
        if (count != 0) {
            ss << ",";
        }
        if (lt.coeff != 0 && lt.coeff != 1) {
            ss << '"' << lt.index << '"' << ":" << "-1";
        }
        else {
            ss << '"' << lt.index << '"' << ":" << lt.coeff;
        }
        count++;
    }
    ss << "}";
}


std::string r1cs_to_json(protoboard<FieldT> pb)
{
    // output inputs, right now need to compile with debug flag so that the `variable_annotations`
    // exists. Having trouble setting that up so will leave for now.
    r1cs_constraint_system<FieldT> constraints = pb.get_constraint_system();
    std::stringstream ss;

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

char* _sha256Constraints()
{
    libff::alt_bn128_pp::init_public_params();
    protoboard<FieldT> pb;
    block_variable<FieldT> input(pb, 256, "input");
    digest_variable<FieldT> output(pb, 256, "output");
    
    auto hash = std::make_shared<sha256_ethereum>(pb, 256, input, output, "cm_hash");

    hash->generate_r1cs_constraints(true);
    auto json = r1cs_to_json(pb);
    auto result = new char[json.size()];
    memcpy(result, json.c_str(), json.size() + 1);
    return result;
}

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

char* _sha256Witness()
{
    protoboard<FieldT> pb;
    std::shared_ptr<sha256_ethereum> hash;

    pb_variable<FieldT> ZERO;
    ZERO.allocate(pb, "ZERO");
    pb.val(ZERO) = 0;
   
    digest_variable<FieldT> output(pb, 256, "output");

   
   //block_variable<FieldT> input =  block_variable<FieldT>(pb, {
   //     from_bits(left, ZERO),
   //     from_bits(right, ZERO)
   // }, "input_variable");

    // hash.reset(new sha256_ethereum(
    //     pb, 256, input, output, "cm_hash"
    // ));

    // hash->generate_r1cs_constraints(true);
    // hash->generate_r1cs_witness();

    // return(array_to_json(hash->pb));
    return "abc";
}

