/**
 * @file pghr13.hpp
 * @author Jacob Eberhardt <jacob.eberhardt@tu-berlin.de
 * @author Dennis Kuhnert <dennis.kuhnert@campus.tu-berlin.de>
 * @date 2017
 */

#pragma once

#ifdef __cplusplus
extern "C" {
#endif

#include "ffi.hpp"

setup_result_t pghr13_bn128_setup(
    const uint8_t* a,
    const uint8_t* b,
    const uint8_t* c,
    int32_t a_len,
    int32_t b_len,
    int32_t c_len,
    int32_t constraints,
    int32_t variables,
    int32_t inputs);

proof_result_t pghr13_bn128_generate_proof(
    buffer_t* pk_buf,
    const uint8_t* public_inputs,
    int32_t public_inputs_length,
    const uint8_t* private_inputs,
    int32_t private_inputs_length);

bool pghr13_bn128_verify(
    buffer_t* vk_buf,
    buffer_t* proof_buf,
    const uint8_t* public_inputs,
    int32_t public_inputs_length);

#ifdef __cplusplus
} // extern "C"
#endif