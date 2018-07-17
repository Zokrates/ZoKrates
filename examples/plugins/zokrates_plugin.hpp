// ZoKrates plugin interface.
//
// @author Aurélien Nicolas <info@nau.re> for QED-it.com
// @date 2018

#include "snark/utils.hpp"

extern "C" {


    // ==== Conversion helpers ====

    // From ZoKrates
    libff::bigint<libff::alt_bn128_r_limbs> libsnarkBigintFromBytes(const uint8_t* _x)
    {
        libff::bigint<libff::alt_bn128_r_limbs> x;

        for (unsigned i = 0; i < 4; i++) {
            for (unsigned j = 0; j < 8; j++) {
                x.data[3 - i] |= uint64_t(_x[i * 8 + j]) << (8 * (7-j));
            }
        }
        return x;
    }


    // The opposite conversion
    void bytesFromLibsnarkBigint(const libff::bigint<libff::alt_bn128_r_limbs> num, uint8_t* out)
    {
        for (unsigned i = 0; i < 4; i++) {
            for (unsigned j = 0; j < 8; j++) {
                out[i * 8 + j] = ( num.data[3 - i] >> (8 * (7-j)) ) & 0xFF;
            }
        }
    }


    // ==== Callback definitions, implemented by ZoKrates ====

    typedef uint8_t FieldBytes[32];

    typedef void (*register_gadget_t)(void *context, char *name, uint64_t n_inputs, uint64_t n_outputs);

    typedef void (*map_variables_t)(void *context, uint64_t first_input, uint64_t first_output, uint64_t first_local);

    typedef void (*add_witness_t)(void *context, uint64_t index, FieldBytes *element);

    typedef void (*add_constraint_t)(void *context, uint8_t is_abc, uint64_t num_constraints, uint64_t *indices, FieldBytes *elements);


    // ==== Helpers to report the content of a protoboard ====

    /** Send all witness values to ZoKrates */
    void report_witness(protoboard<FieldT> &pb, add_witness_t add_witness, void *context) {
        FieldBytes tmp_bytes; // A stack variable to be copied by the callback

        // Go through the values and interpret them as input, local, or output
        for (size_t index = 0 ; index <= pb.num_variables(); ++index) {
            bytesFromLibsnarkBigint(pb.val(index).as_bigint(), tmp_bytes);
            add_witness(context, index, &tmp_bytes);
        }
    }


    /** Send all constraints to ZoKrates */
    void report_constraints(const protoboard<FieldT> &pb, add_constraint_t add_constraint, void *context) {

        /** Closure: send a row of a matrix */
        auto send_row = [&] (
                const vector<libsnark::linear_term<FieldT>> &terms,
                uint8_t is_abc
        ) {
            vector<uint64_t> indices; indices.resize(terms.size());
            vector<array<uint8_t, 32>> coeffs; coeffs.resize(terms.size());
            for (size_t i = 0; i < terms.size(); i++) {
                indices[i] = terms[i].index;
                bytesFromLibsnarkBigint(terms[i].coeff.as_bigint(), coeffs[i].data());
            }
            add_constraint(context, is_abc, terms.size(), indices.data(), (FieldBytes *) coeffs.front().data());
        };

        // Send all rows of all three matrices
        auto constraints = pb.get_constraint_system().constraints;
        for (auto constraint = constraints.begin(); constraint != constraints.end(); constraint++) {
            send_row(constraint->a.terms, /*is_abc*/ 0);
            send_row(constraint->b.terms, /*is_abc*/ 1);
            send_row(constraint->c.terms, /*is_abc*/ 2);
        }
    }


    // ==== Interface to Zokrates ====

    bool zokrates_init_gadgets(
            register_gadget_t register_gadget,
            void *context
    );


    bool zokrates_make_witness(
            char *gadget_name,
            FieldBytes *inputs_bytes,
            uint64_t  inputs_size,
            // Callback and its context
            map_variables_t map_variables,
            add_witness_t add_witness,
            void *context
    );


    bool zokrates_make_constraints(
            char *gadget_name,
            uint64_t  inputs_size,
            // Callback and its context
            map_variables_t map_variables,
            add_constraint_t add_constraint,
            void *context
    );

}
