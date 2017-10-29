/**
 * @file wraplibsnark.hpp
 * @author Jacob Eberhardt <jacob.eberhardt@tu-berlin.de
 * @author Dennis Kuhnert <dennis.kuhnert@campus.tu-berlin.de>
 * @date 2017
 */

#ifdef __cplusplus
extern "C" {
#endif

#include <stdbool.h>
#include <stdint.h>

bool _setup(const uint8_t* A,
            const uint8_t* B,
            const uint8_t* C,
            int constraints,
            int variables,
            int inputs,
            const char* pk_path,
            const char* vk_path
          );

bool _generate_proof(const char* pk_path,
            const uint8_t* public_inputs,
            int public_inputs_length,
            const uint8_t* private_inputs,
            int private_inputs_length
          );

#ifdef __cplusplus
} // extern "C"
#endif
