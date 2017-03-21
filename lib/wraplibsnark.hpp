/**
 * @file wraplibsnark.hpp
 * @author Dennis Kuhnert <dennis.kuhnert@campus.tu-berlin.de>
 * @date 2017
 */

#ifdef __cplusplus
extern "C" {
#endif

#include <stdbool.h>
#include <stdint.h>

bool _run_libsnark(const uint8_t* A,
                  const uint8_t* B,
                  const uint8_t* C,
                  const uint8_t* witness,
                  int constraints,
                  int variables);

#ifdef __cplusplus
} // extern "C"
#endif
