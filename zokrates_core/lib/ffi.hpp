#pragma once

#include <cstdlib>
#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

struct buffer_t {
    uint8_t* data;
    int32_t length;
};

struct setup_result_t {
    buffer_t vk;
    buffer_t pk;
    setup_result_t(buffer_t& vk_buf, buffer_t& pk_buf)
        : vk(vk_buf)
        , pk(pk_buf)
    {
    }
};

struct proof_result_t {
    buffer_t proof;
    proof_result_t(buffer_t& proof_buf)
        : proof(proof_buf)
    {
    }
};

void __free(uint8_t* ptr);

#ifdef __cplusplus
} // extern "C"
#endif