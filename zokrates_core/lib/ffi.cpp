#include "ffi.hpp"

void __alloc(buffer_t* buffer, size_t length) {
    buffer->data = (uint8_t*)malloc(length);
    buffer->length = length;
}

void __free(uint8_t* ptr) {
  free(ptr);
}