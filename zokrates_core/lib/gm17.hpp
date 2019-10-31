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
          int32_t A_len,
          int32_t B_len,
          int32_t C_len,
          int32_t constraints,
          int32_t variables,
          int32_t inputs,
          uint8_t* vk_buf,
          uint8_t* pk_buf 
        );

void _gm17_generate_proof(
          const uint8_t* pk_buf,
          int32_t pk_buf_length,
          const uint8_t* public_inputs,
          int32_t public_inputs_length,
          const uint8_t* private_inputs,
          int32_t private_inputs_length,
          uint8_t* proof_buf
);

#ifdef __cplusplus
} // extern "C"
#endif