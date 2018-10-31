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

char* _sha256Constraints();
char* _sha256Witness(const uint8_t* input, int input_length);

char* _shaEth256Constraints();
char* _shaEth256Witness(const uint8_t* input, int input_length);

#ifdef __cplusplus
} // extern "C"
#endif
