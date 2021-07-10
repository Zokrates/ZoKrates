#include "ffi.hpp"

void c_free(uint8_t* ptr)
{
    free(ptr);
}