#pragma once

#include "ffi.hpp"

#include <cassert>
#include <iomanip>
#include <iostream>
#include <sstream>
#include <string>

// conversion byte[N] -> libsnark bigint
template <mp_size_t N>
libff::bigint<N> to_libff_bigint(const uint8_t* input)
{
    libff::bigint<N> x;
    for (unsigned i = 0; i < N; i++) {
        for (unsigned j = 0; j < 8; j++) {
            x.data[N - 1 - i] |= uint64_t(input[i * 8 + j]) << (8 * (7 - j));
        }
    }
    return x;
}

// conversion libsnark bigint -> byte[N]
template <mp_size_t N>
void from_libff_bigint(libff::bigint<N> x, uint8_t* out)
{
    for (unsigned i = 0; i < N; i++) {
        for (unsigned j = 0; j < 8; j++) {
            out[i * 8 + j] = uint8_t(uint64_t(x.data[N - 1 - i]) >> (8 * (7 - j)));
        }
    }
}

template <mp_size_t Q, typename G1>
void serialize_g1_affine(G1 point, uint8_t*& buffer)
{
    const size_t ELEMENT_SIZE = Q * sizeof(mp_limb_t);

    G1 aff = point;
    aff.to_affine_coordinates();

    auto x = aff.X.as_bigint();
    auto y = aff.Y.as_bigint();

    from_libff_bigint<Q>(x, buffer);
    buffer += ELEMENT_SIZE;
    from_libff_bigint<Q>(y, buffer);
    buffer += ELEMENT_SIZE;
}

template <mp_size_t Q, typename G2>
void serialize_g2_affine(G2 point, uint8_t*& buffer)
{
    const size_t ELEMENT_SIZE = Q * sizeof(mp_limb_t);

    G2 aff = point;
    aff.to_affine_coordinates();

    auto x0 = aff.X.c0.as_bigint();
    auto x1 = aff.X.c1.as_bigint();
    auto y0 = aff.Y.c0.as_bigint();
    auto y1 = aff.Y.c1.as_bigint();

    from_libff_bigint<Q>(x0, buffer);
    buffer += ELEMENT_SIZE;
    from_libff_bigint<Q>(x1, buffer);
    buffer += ELEMENT_SIZE;
    from_libff_bigint<Q>(y0, buffer);
    buffer += ELEMENT_SIZE;
    from_libff_bigint<Q>(y1, buffer);
    buffer += ELEMENT_SIZE;
}

template <mp_size_t Q, typename Fq, typename G1>
G1 deserialize_g1_affine(uint8_t*& buffer)
{
    const size_t ELEMENT_SIZE = Q * sizeof(mp_limb_t);

    auto x = to_libff_bigint<Q>(buffer);
    buffer += ELEMENT_SIZE;
    auto y = to_libff_bigint<Q>(buffer);
    buffer += ELEMENT_SIZE;

    return G1(Fq(x), Fq(y), Fq::one());
}

template <mp_size_t Q, typename Fq2, typename G2>
G2 deserialize_g2_affine(uint8_t*& buffer)
{
    const size_t ELEMENT_SIZE = Q * sizeof(mp_limb_t);

    auto x0 = to_libff_bigint<Q>(buffer);
    buffer += ELEMENT_SIZE;
    auto x1 = to_libff_bigint<Q>(buffer);
    buffer += ELEMENT_SIZE;
    auto y0 = to_libff_bigint<Q>(buffer);
    buffer += ELEMENT_SIZE;
    auto y1 = to_libff_bigint<Q>(buffer);
    buffer += ELEMENT_SIZE;

    auto x = Fq2(x0, x1);
    auto y = Fq2(y0, y1);
    return G2(x, y, Fq2::one());
}

template <template <typename ppT> class ConstraintSystem, mp_size_t R, typename ppT>
ConstraintSystem<ppT> create_constraint_system(const uint8_t* a,
    const uint8_t* b,
    const uint8_t* c,
    int32_t a_len,
    int32_t b_len,
    int32_t c_len,
    int32_t constraints,
    int32_t variables,
    int32_t inputs)
{
    ConstraintSystem<ppT> cs;
    cs.primary_input_size = inputs;
    cs.auxiliary_input_size = variables - inputs - 1; // ~one not included

    struct vvmap_t {
        int constraint_id;
        int variable_id;
        uint8_t variable_value[R * sizeof(mp_limb_t)];
    };

    const vvmap_t* a_vvmap = (vvmap_t*)a;
    const vvmap_t* b_vvmap = (vvmap_t*)b;
    const vvmap_t* c_vvmap = (vvmap_t*)c;

    int a_id = 0;
    int b_id = 0;
    int c_id = 0;

    for (int row = 0; row < constraints; row++) {
        linear_combination<libff::Fr<ppT>> lin_comb_a, lin_comb_b, lin_comb_c;
        while (a_id < a_len && a_vvmap[a_id].constraint_id == row) {
            libff::bigint<R> value = to_libff_bigint<R>(a_vvmap[a_id].variable_value);
            if (!value.is_zero()) {
                lin_comb_a.add_term(a_vvmap[a_id].variable_id, value);
            }
            a_id++;
        }
        while (b_id < b_len && b_vvmap[b_id].constraint_id == row) {
            libff::bigint<R> value = to_libff_bigint<R>(b_vvmap[b_id].variable_value);
            if (!value.is_zero()) {
                lin_comb_b.add_term(b_vvmap[b_id].variable_id, value);
            }
            b_id++;
        }
        while (c_id < c_len && c_vvmap[c_id].constraint_id == row) {
            libff::bigint<R> value = to_libff_bigint<R>(c_vvmap[c_id].variable_value);
            if (!value.is_zero()) {
                lin_comb_c.add_term(c_vvmap[c_id].variable_id, value);
            }
            c_id++;
        }
        cs.add_constraint(r1cs_constraint<libff::Fr<ppT>>(lin_comb_a, lin_comb_b, lin_comb_c));
    }
    return cs;
}

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
    size_t length = tmp.length();

    buffer_t buffer;
    buffer.data = (uint8_t*)malloc(length);
    buffer.length = length;

    tmp.copy(reinterpret_cast<char*>(buffer.data), buffer.length);
    return buffer;
}