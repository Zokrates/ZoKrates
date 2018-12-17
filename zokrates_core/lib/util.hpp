#pragma once

// contains definition of alt_bn128 ec public parameters
#include "libff/algebra/curves/alt_bn128/alt_bn128_pp.hpp"
#include <fstream>
#include <iostream>
#include <cassert>
#include <iomanip>

libff::bigint<libff::alt_bn128_r_limbs> libsnarkBigintFromBytes(const uint8_t* _x);

std::string HexStringFromLibsnarkBigint(libff::bigint<libff::alt_bn128_r_limbs> _x);

std::string outputPointG1AffineAsHex(libff::alt_bn128_G1 _p);

std::string outputPointG1AffineAsHexJson(libff::alt_bn128_G1 _p);

std::string outputPointG2AffineAsHex(libff::alt_bn128_G2 _p);

std::string outputPointG2AffineAsHexJson(libff::alt_bn128_G2 _p);

template<typename T>
void writeToFile(std::string path, T& obj) {
    std::stringstream ss;
    ss << obj;
    std::ofstream fh;
    fh.open(path, std::ios::binary);
    ss.rdbuf()->pubseekpos(0, std::ios_base::out);
    fh << ss.rdbuf();
    fh.flush();
    fh.close();
}

template<typename T>
T loadFromFile(std::string path) {
    std::stringstream ss;
    std::ifstream fh(path, std::ios::binary);

    assert(fh.is_open());

    ss << fh.rdbuf();
    fh.close();

    ss.rdbuf()->pubseekpos(0, std::ios_base::in);

    T obj;
    ss >> obj;

    return obj;
}