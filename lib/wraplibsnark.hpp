/**
 * @file wraplibsnark.hpp
 * @author Dennis Kuhnert <dennis.kuhnert@campus.tu-berlin.de>
 * @date 2017
 */

#ifdef __cplusplus
extern "C" {
#endif

#include <stdbool.h>

bool _run_libsnark(const char* A,
                  const char* B,
                  const char* C,
                  const char* witness,
                  int constraints,
                  int variables);

#ifdef __cplusplus
} // extern "C"
#endif
