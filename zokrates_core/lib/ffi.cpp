#include "ffi.hpp"

void __free(uint8_t* ptr)
{
    free(ptr);
}