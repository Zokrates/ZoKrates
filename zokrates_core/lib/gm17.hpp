/**
 * @file gm17.hpp
 * @author Jacob Eberhardt <jacob.eberhardt@tu-berlin.de
 * @author Dennis Kuhnert <dennis.kuhnert@campus.tu-berlin.de>
 * @date 2017
 */

#pragma once

#ifdef __cplusplus
extern "C" {
#endif

#include <stdbool.h>
#include <stdint.h>

void _gm17_setup(const uint8_t* A,
          const uint8_t* B,
          const uint8_t* C,
          int A_len,
          int B_len,
          int C_len,
          int constraints,
          int variables,
          int inputs,
          uint8_t* vk_buf,
          uint8_t* pk_buf 
        );

void _gm17_generate_proof(
          const uint8_t* pk_buf,
          int pk_buf_length,
          const uint8_t* public_inputs,
          int public_inputs_length,
          const uint8_t* private_inputs,
          int private_inputs_length,
          uint8_t* proof_buf
);

#ifdef __cplusplus
} // extern "C"
#endif