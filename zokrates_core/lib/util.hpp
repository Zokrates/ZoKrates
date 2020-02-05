#pragma once

// contains definitions of alt_bn128 ec public parameters
#include "libff/algebra/curves/alt_bn128/alt_bn128_pp.hpp"

#include <cassert>
#include <iostream>
#include <string>
#include <sstream>
#include <iomanip>

libff::bigint<libff::alt_bn128_r_limbs> libsnarkBigintFromBytes(const uint8_t* _x);
std::string HexStringFromLibsnarkBigint(libff::bigint<libff::alt_bn128_r_limbs> _x);
std::string outputInputAsHex(libff::bigint<libff::alt_bn128_r_limbs> _x);
std::string outputPointG1AffineAsHex(libff::alt_bn128_G1 _p);
std::string outputPointG1AffineAsHexJson(libff::alt_bn128_G1 _p);
std::string outputPointG2AffineAsHex(libff::alt_bn128_G2 _p);
std::string outputPointG2AffineAsHexJson(libff::alt_bn128_G2 _p);