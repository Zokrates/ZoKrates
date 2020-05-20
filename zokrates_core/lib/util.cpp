/**
 * @file util.cpp
 * @author Jacob Eberhardt <jacob.eberhardt@tu-berlin.de
 * @author Dennis Kuhnert <dennis.kuhnert@campus.tu-berlin.de>
 * @date 2017
 */

#include "util.hpp"

// conversion byte[32] <-> libsnark bigint.
libff::bigint<libff::alt_bn128_r_limbs> libsnarkBigintFromBytes(const uint8_t* _x)
{
    libff::bigint<libff::alt_bn128_r_limbs> x;
    for (unsigned i = 0; i < 4; i++) {
        for (unsigned j = 0; j < 8; j++) {
            x.data[3 - i] |= uint64_t(_x[i * 8 + j]) << (8 * (7 - j));
        }
    }
    return x;
}

std::string toHexString(const std::string& in)
{
    std::ostringstream out;
    out << std::setfill('0');
    for (unsigned char const& c : in) {
        out << std::hex << std::setw(2) << static_cast<unsigned int>(c);
    }
    return out.str();
}

std::string HexStringFromLibsnarkBigint(libff::bigint<libff::alt_bn128_r_limbs> _x)
{
    uint8_t x[32];
    for (unsigned i = 0; i < 4; i++) {
        for (unsigned j = 0; j < 8; j++) {
            x[i * 8 + j] = uint8_t(uint64_t(_x.data[3 - i]) >> (8 * (7 - j)));
        }
    }
    std::string tmp((char*)x, 32);
    return toHexString(tmp);
}

std::string outputInputAsHex(libff::bigint<libff::alt_bn128_r_limbs> _x)
{
    return "\"0x" + HexStringFromLibsnarkBigint(_x) + "\"";
}

std::string outputPointG1AffineAsHex(libff::alt_bn128_G1 _p)
{
    libff::alt_bn128_G1 aff = _p;
    aff.to_affine_coordinates();
    return "0x" + HexStringFromLibsnarkBigint(aff.X.as_bigint()) + ", 0x" + HexStringFromLibsnarkBigint(aff.Y.as_bigint());
}

std::string outputPointG1AffineAsHexJson(libff::alt_bn128_G1 _p)
{
    libff::alt_bn128_G1 aff = _p;
    aff.to_affine_coordinates();
    return "[\"0x" + HexStringFromLibsnarkBigint(aff.X.as_bigint()) + "\", \"0x" + HexStringFromLibsnarkBigint(aff.Y.as_bigint()) + "\"]";
}

std::string outputPointG2AffineAsHex(libff::alt_bn128_G2 _p)
{
    libff::alt_bn128_G2 aff = _p;
    aff.to_affine_coordinates();
    return "[0x" + HexStringFromLibsnarkBigint(aff.X.c1.as_bigint()) + ", 0x" + HexStringFromLibsnarkBigint(aff.X.c0.as_bigint()) + "], [0x" + HexStringFromLibsnarkBigint(aff.Y.c1.as_bigint()) + ", 0x" + HexStringFromLibsnarkBigint(aff.Y.c0.as_bigint()) + "]";
}

std::string outputPointG2AffineAsHexJson(libff::alt_bn128_G2 _p)
{
    libff::alt_bn128_G2 aff = _p;
    aff.to_affine_coordinates();
    return "[[\"0x" + HexStringFromLibsnarkBigint(aff.X.c1.as_bigint()) + "\", \"0x" + HexStringFromLibsnarkBigint(aff.X.c0.as_bigint()) + "\"], [\"0x" + HexStringFromLibsnarkBigint(aff.Y.c1.as_bigint()) + "\", \"0x" + HexStringFromLibsnarkBigint(aff.Y.c0.as_bigint()) + "\"]]";
}