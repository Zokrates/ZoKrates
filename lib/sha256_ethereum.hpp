#ifdef __cplusplus
extern "C" {
#endif

pb_variable_array<FieldT> from_bits(std::vector<bool> bits, pb_variable<FieldT>& ZERO);

bool _generate_proof(const char* pk_path,
            const uint8_t* public_inputs,
            int public_inputs_length,
            const uint8_t* private_inputs,
            int private_inputs_length
          );

class sha256_ethereum : gadget<FieldT> {};

vector<unsigned long> bit_list_to_ints(vector<bool> bit_list, const size_t wordsize);
pb_variable_array<FieldT> from_bits(std::vector<bool> bits, pb_variable<FieldT>& ZERO);

#ifdef __cplusplus
} // extern "C"
#endif
