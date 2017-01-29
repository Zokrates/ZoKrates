#ifdef __cplusplus
extern "C" {
#endif

#include <stdbool.h>

bool _run_libsnark(const int* A,
                  const int* B,
                  const int* C,
                  const int* witness,
                  int constraints,
                  int variables);

#ifdef __cplusplus
} // extern "C"
#endif
