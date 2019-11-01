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

struct buffer_t {
  uint8_t* data;
  int32_t length;

  void alloc(int32_t length) {
    this->data = (uint8_t*)malloc(length);
    this->length = length;
  }
};

struct gm17_setup_export_t {
  buffer_t vk;
  buffer_t pk;

  gm17_setup_export_t(buffer_t& vk_buf, buffer_t& pk_buf) : vk(vk_buf), pk(pk_buf) { }
};

struct gm17_generate_proof_t {
  buffer_t proof;

  gm17_generate_proof_t(buffer_t& proof_buf) : proof(proof_buf) { }
};

gm17_setup_export_t _gm17_setup(const uint8_t* A,
          const uint8_t* B,
          const uint8_t* C,
          int32_t A_len,
          int32_t B_len,
          int32_t C_len,
          int32_t constraints,
          int32_t variables,
          int32_t inputs
);

gm17_generate_proof_t _gm17_generate_proof(
          buffer_t* pk_buf,
          const uint8_t* public_inputs,
          int32_t public_inputs_length,
          const uint8_t* private_inputs,
          int32_t private_inputs_length
);

#ifdef __cplusplus
} // extern "C"
#endif