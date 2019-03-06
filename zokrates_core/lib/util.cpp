/**
 * @file wraplibsnark.cpp
 * @author Jacob Eberhardt <jacob.eberhardt@tu-berlin.de
 * @author Dennis Kuhnert <dennis.kuhnert@campus.tu-berlin.de>
 * @date 2017
 */

#include "util.hpp"

using namespace std;

// conversion byte[32] <-> libsnark bigint.
libff::bigint<libff::alt_bn128_r_limbs> libsnarkBigintFromBytes(const uint8_t* _x)
{
  libff::bigint<libff::alt_bn128_r_limbs> x;

  for (unsigned i = 0; i < 4; i++) {
    for (unsigned j = 0; j < 8; j++) {
      x.data[3 - i] |= uint64_t(_x[i * 8 + j]) << (8 * (7-j));
    }
  }
  
  return x;
}

std::string HexStringFromLibsnarkBigint(libff::bigint<libff::alt_bn128_r_limbs> _x){
    uint8_t x[32];
    for (unsigned i = 0; i < 4; i++)
        for (unsigned j = 0; j < 8; j++)
          x[i * 8 + j] = uint8_t(uint64_t(_x.data[3 - i]) >> (8 * (7 - j)));

    std::stringstream ss;
    ss << std::setfill('0');
    for (unsigned i = 0; i<32; i++) {
            ss << std::hex << std::setw(2) << (int)x[i];
    }

    return ss.str();
}

std::string outputPointG1AffineAsHex(libff::alt_bn128_G1 _p)
{
        libff::alt_bn128_G1 aff = _p;
        aff.to_affine_coordinates();
        return
                "0x" +
                HexStringFromLibsnarkBigint(aff.X.as_bigint()) +
                ", 0x" +
                HexStringFromLibsnarkBigint(aff.Y.as_bigint());
}

std::string outputPointG1AffineAsHexJson(libff::alt_bn128_G1 _p)
{
        libff::alt_bn128_G1 aff = _p;
        aff.to_affine_coordinates();
        return
                "[\"0x" +
                HexStringFromLibsnarkBigint(aff.X.as_bigint()) +
                "\", \"0x" +
                HexStringFromLibsnarkBigint(aff.Y.as_bigint())+"\"]";
}

std::string outputPointG2AffineAsHex(libff::alt_bn128_G2 _p)
{
        libff::alt_bn128_G2 aff = _p;
        aff.to_affine_coordinates();
        return
                "[0x" +
                HexStringFromLibsnarkBigint(aff.X.c1.as_bigint()) + ", 0x" +
                HexStringFromLibsnarkBigint(aff.X.c0.as_bigint()) + "], [0x" +
                HexStringFromLibsnarkBigint(aff.Y.c1.as_bigint()) + ", 0x" +
                HexStringFromLibsnarkBigint(aff.Y.c0.as_bigint()) + "]";
}

std::string outputPointG2AffineAsHexJson(libff::alt_bn128_G2 _p)
{
        libff::alt_bn128_G2 aff = _p;
        aff.to_affine_coordinates();
        return
                "[[\"0x" +
                HexStringFromLibsnarkBigint(aff.X.c1.as_bigint()) + "\", \"0x" +
                HexStringFromLibsnarkBigint(aff.X.c0.as_bigint()) + "\"], [\"0x" +
                HexStringFromLibsnarkBigint(aff.Y.c1.as_bigint()) + "\", \"0x" +
                HexStringFromLibsnarkBigint(aff.Y.c0.as_bigint()) + "\"]]";
}
