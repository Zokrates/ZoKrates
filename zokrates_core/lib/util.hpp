#pragma once

// contains definitions of alt_bn128 ec public parameters
#include "ffi.hpp"
#include "libff/algebra/curves/alt_bn128/alt_bn128_pp.hpp"

#include <cassert>
#include <iomanip>
#include <iostream>
#include <sstream>
#include <string>

libff::bigint<libff::alt_bn128_r_limbs> libsnarkBigintFromBytes(const uint8_t* _x);
std::string toHex(const std::string& s);
std::string HexStringFromLibsnarkBigint(libff::bigint<libff::alt_bn128_r_limbs> _x);
std::string outputInputAsHex(libff::bigint<libff::alt_bn128_r_limbs> _x);
std::string outputPointG1AffineAsHex(libff::alt_bn128_G1 _p);
std::string outputPointG1AffineAsHexJson(libff::alt_bn128_G1 _p);
std::string outputPointG2AffineAsHex(libff::alt_bn128_G2 _p);
std::string outputPointG2AffineAsHexJson(libff::alt_bn128_G2 _p);

template <typename T>
inline void from_buffer(buffer_t* buffer, T& t)
{
    std::string tmp((char*)buffer->data, buffer->length);
    std::stringstream ss(tmp);
    ss >> t;
}

template <typename T>
inline buffer_t create_buffer(T& t)
{
    std::stringstream ss;
    ss << t;

    std::string tmp = ss.str();

    buffer_t buffer;
    make_buffer(&buffer, tmp.length());

    tmp.copy(reinterpret_cast<char*>(buffer.data), buffer.length);
    return buffer;
}