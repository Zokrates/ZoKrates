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

setup_result_t pghr13_setup(
    const uint8_t* A,
    const uint8_t* B,
    const uint8_t* C,
    int32_t A_len,
    int32_t B_len,
    int32_t C_len,
    int32_t constraints,
    int32_t variables,
    int32_t inputs
);

proof_result_t pghr13_generate_proof(
    buffer_t* pk_buf,
    const uint8_t* public_inputs,
    int32_t public_inputs_length,
    const uint8_t* private_inputs,
    int32_t private_inputs_length
);

#ifdef __cplusplus
} // extern "C"
#endif