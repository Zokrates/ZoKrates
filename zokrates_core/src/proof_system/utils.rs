use field::Field;
use flat_absy::flat_variable::FlatVariable;
use std::cmp::max;
use std::ffi::CString;

// utility function. Converts a Fields vector-based byte representation to fixed size array.
fn vec_as_u8_32_array(vec: &Vec<u8>) -> [u8; 32] {
    assert!(vec.len() <= 32);
    let mut array = [0u8; 32];
    for (index, byte) in vec.iter().enumerate() {
        array[31 - index] = *byte;
    }
    array
}

// proof-system-independent preparation for the setup phase
pub fn prepare_setup<T: Field>(
    variables: Vec<FlatVariable>,
    a: Vec<Vec<(usize, T)>>,
    b: Vec<Vec<(usize, T)>>,
    c: Vec<Vec<(usize, T)>>,
    num_inputs: usize,
    pk_path: &str,
    vk_path: &str,
) -> (
    Vec<u8>,
    Vec<u8>,
    Vec<u8>,
    Vec<(i32, i32, [u8; 32])>,
    Vec<(i32, i32, [u8; 32])>,
    Vec<(i32, i32, [u8; 32])>,
    usize,
    usize,
    usize,
    CString,
    CString,
) {
    let num_constraints = a.len();
    let num_variables = variables.len();

    // Create single A,B,C vectors of tuples (constraint_number, variable_id, variable_value)
    let mut a_vec = vec![];
    let mut b_vec = vec![];
    let mut c_vec = vec![];
    for row in 0..num_constraints {
        for &(idx, ref val) in &a[row] {
            a_vec.push((
                row as i32,
                idx as i32,
                vec_as_u8_32_array(&val.into_byte_vector()),
            ));
        }
        for &(idx, ref val) in &b[row] {
            b_vec.push((
                row as i32,
                idx as i32,
                vec_as_u8_32_array(&val.into_byte_vector()),
            ));
        }
        for &(idx, ref val) in &c[row] {
            c_vec.push((
                row as i32,
                idx as i32,
                vec_as_u8_32_array(&val.into_byte_vector()),
            ));
        }
    }

    // Sizes and offsets in bytes for our struct {row, id, value}
    // We're building { i32, i32, i8[32] }
    const STRUCT_SIZE: usize = 40;

    const ROW_SIZE: usize = 4;

    const IDX_SIZE: usize = 4;
    const IDX_OFFSET: usize = 4;

    const VALUE_SIZE: usize = 32;
    const VALUE_OFFSET: usize = 8;

    // Convert above A,B,C vectors to byte arrays for cpp
    let mut a_arr: Vec<u8> = vec![0u8; STRUCT_SIZE * a_vec.len()];
    let mut b_arr: Vec<u8> = vec![0u8; STRUCT_SIZE * b_vec.len()];
    let mut c_arr: Vec<u8> = vec![0u8; STRUCT_SIZE * c_vec.len()];
    use std::mem::transmute;
    for (id, (row, idx, val)) in a_vec.iter().enumerate() {
        let row_bytes: [u8; ROW_SIZE] = unsafe { transmute(row.to_le()) };
        let idx_bytes: [u8; IDX_SIZE] = unsafe { transmute(idx.to_le()) };

        for x in 0..ROW_SIZE {
            a_arr[id * STRUCT_SIZE + x] = row_bytes[x];
        }
        for x in 0..IDX_SIZE {
            a_arr[id * STRUCT_SIZE + x + IDX_OFFSET] = idx_bytes[x];
        }
        for x in 0..VALUE_SIZE {
            a_arr[id * STRUCT_SIZE + x + VALUE_OFFSET] = val[x];
        }
    }
    for (id, (row, idx, val)) in b_vec.iter().enumerate() {
        let row_bytes: [u8; ROW_SIZE] = unsafe { transmute(row.to_le()) };
        let idx_bytes: [u8; IDX_SIZE] = unsafe { transmute(idx.to_le()) };

        for x in 0..ROW_SIZE {
            b_arr[id * STRUCT_SIZE + x] = row_bytes[x];
        }
        for x in 0..IDX_SIZE {
            b_arr[id * STRUCT_SIZE + x + IDX_OFFSET] = idx_bytes[x];
        }
        for x in 0..VALUE_SIZE {
            b_arr[id * STRUCT_SIZE + x + VALUE_OFFSET] = val[x];
        }
    }
    for (id, (row, idx, val)) in c_vec.iter().enumerate() {
        let row_bytes: [u8; ROW_SIZE] = unsafe { transmute(row.to_le()) };
        let idx_bytes: [u8; IDX_SIZE] = unsafe { transmute(idx.to_le()) };

        for x in 0..ROW_SIZE {
            c_arr[id * STRUCT_SIZE + x] = row_bytes[x];
        }
        for x in 0..IDX_SIZE {
            c_arr[id * STRUCT_SIZE + x + IDX_OFFSET] = idx_bytes[x];
        }
        for x in 0..VALUE_SIZE {
            c_arr[id * STRUCT_SIZE + x + VALUE_OFFSET] = val[x];
        }
    }

    // convert String slices to 'CString's
    let pk_path_cstring = CString::new(pk_path).unwrap();
    let vk_path_cstring = CString::new(vk_path).unwrap();

    (
        a_arr,
        b_arr,
        c_arr,
        a_vec,
        b_vec,
        c_vec,
        num_constraints,
        num_variables,
        num_inputs,
        pk_path_cstring,
        vk_path_cstring,
    )
}

// proof-system-independent preparation for proof generation
pub fn prepare_generate_proof<T: Field>(
    pk_path: &str,
    proof_path: &str,
    public_inputs: Vec<T>,
    private_inputs: Vec<T>,
) -> (CString, CString, Vec<[u8; 32]>, usize, Vec<[u8; 32]>, usize) {
    let pk_path_cstring = CString::new(pk_path).unwrap();
    let proof_path_cstring = CString::new(proof_path).unwrap();

    let public_inputs_length = public_inputs.len();
    let private_inputs_length = private_inputs.len();

    let mut public_inputs_arr: Vec<[u8; 32]> = vec![[0u8; 32]; public_inputs_length];
    // length must not be zero here, so we apply the max function
    let mut private_inputs_arr: Vec<[u8; 32]> = vec![[0u8; 32]; max(private_inputs_length, 1)];

    //convert inputs
    for (index, value) in public_inputs.into_iter().enumerate() {
        public_inputs_arr[index] = vec_as_u8_32_array(&value.into_byte_vector());
    }
    for (index, value) in private_inputs.into_iter().enumerate() {
        private_inputs_arr[index] = vec_as_u8_32_array(&value.into_byte_vector());
    }

    (
        pk_path_cstring,
        proof_path_cstring,
        public_inputs_arr,
        public_inputs_length,
        private_inputs_arr,
        private_inputs_length,
    )
}

pub const SOLIDITY_PAIRING_LIB : &str = r#"// This file is MIT Licensed.
//
// Copyright 2017 Christian Reitwiessner
// Permission is hereby granted, free of charge, to any person obtaining a copy of this software and associated documentation files (the "Software"), to deal in the Software without restriction, including without limitation the rights to use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is furnished to do so, subject to the following conditions:
// The above copyright notice and this permission notice shall be included in all copies or substantial portions of the Software.
// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.

pragma solidity ^0.4.14;
library Pairing {
    struct G1Point {
        uint X;
        uint Y;
    }
    // Encoding of field elements is: X[0] * z + X[1]
    struct G2Point {
        uint[2] X;
        uint[2] Y;
    }
    /// @return the generator of G1
    function P1() pure internal returns (G1Point) {
        return G1Point(1, 2);
    }
    /// @return the generator of G2
    function P2() pure internal returns (G2Point) {
        return G2Point(
            [11559732032986387107991004021392285783925812861821192530917403151452391805634,
             10857046999023057135944570762232829481370756359578518086990519993285655852781],
            [4082367875863433681332203403145435568316851327593401208105741076214120093531,
             8495653923123431417604973247489272438418190587263600148770280649306958101930]
        );
    }
    /// @return the negation of p, i.e. p.addition(p.negate()) should be zero.
    function negate(G1Point p) pure internal returns (G1Point) {
        // The prime q in the base field F_q for G1
        uint q = 21888242871839275222246405745257275088696311157297823662689037894645226208583;
        if (p.X == 0 && p.Y == 0)
            return G1Point(0, 0);
        return G1Point(p.X, q - (p.Y % q));
    }
    /// @return the sum of two points of G1
    function addition(G1Point p1, G1Point p2) internal returns (G1Point r) {
        uint[4] memory input;
        input[0] = p1.X;
        input[1] = p1.Y;
        input[2] = p2.X;
        input[3] = p2.Y;
        bool success;
        assembly {
            success := call(sub(gas, 2000), 6, 0, input, 0xc0, r, 0x60)
            // Use "invalid" to make gas estimation work
            switch success case 0 { invalid() }
        }
        require(success);
    }
    /// @return the sum of two points of G2
    function addition(G2Point p1, G2Point p2) internal returns (G2Point r) {
        uint[4] memory inputX;
        inputX[0] = p1.X[0];
        inputX[1] = p1.X[1];
        inputX[2] = p2.X[0];
        inputX[3] = p2.X[1];
        
        uint[4] memory inputY;
        inputX[0] = p1.Y[0];
        inputX[1] = p1.Y[1];
        inputX[2] = p2.Y[0];
        inputX[3] = p2.Y[1];
        
        G1Point memory resX;
        G1Point memory resY;
        
        bool success;
        assembly {
            success := call(sub(gas, 2000), 6, 0, inputX, 0xc0, resX, 0x60)
            // Use "invalid" to make gas estimation work
            switch success case 0 { invalid() }
        }
        require(success);
        assembly {
            success := call(sub(gas, 2000), 6, 0, inputY, 0xc0, resY, 0x60)
            // Use "invalid" to make gas estimation work
            switch success case 0 { invalid() }
        }
        require(success);
        r.X[0] = resX.X;
        r.X[1] = resX.Y;
        r.Y[0] = resY.X;
        r.Y[1] = resY.Y;
    }
    /// @return the product of a point on G1 and a scalar, i.e.
    /// p == p.scalar_mul(1) and p.addition(p) == p.scalar_mul(2) for all points p.
    function scalar_mul(G1Point p, uint s) internal returns (G1Point r) {
        uint[3] memory input;
        input[0] = p.X;
        input[1] = p.Y;
        input[2] = s;
        bool success;
        assembly {
            success := call(sub(gas, 2000), 7, 0, input, 0x80, r, 0x60)
            // Use "invalid" to make gas estimation work
            switch success case 0 { invalid() }
        }
        require (success);
    }
    /// @return the result of computing the pairing check
    /// e(p1[0], p2[0]) *  .... * e(p1[n], p2[n]) == 1
    /// For example pairing([P1(), P1().negate()], [P2(), P2()]) should
    /// return true.
    function pairing(G1Point[] p1, G2Point[] p2) internal returns (bool) {
        require(p1.length == p2.length);
        uint elements = p1.length;
        uint inputSize = elements * 6;
        uint[] memory input = new uint[](inputSize);
        for (uint i = 0; i < elements; i++)
        {
            input[i * 6 + 0] = p1[i].X;
            input[i * 6 + 1] = p1[i].Y;
            input[i * 6 + 2] = p2[i].X[0];
            input[i * 6 + 3] = p2[i].X[1];
            input[i * 6 + 4] = p2[i].Y[0];
            input[i * 6 + 5] = p2[i].Y[1];
        }
        uint[1] memory out;
        bool success;
        assembly {
            success := call(sub(gas, 2000), 8, 0, add(input, 0x20), mul(inputSize, 0x20), out, 0x20)
            // Use "invalid" to make gas estimation work
            switch success case 0 { invalid() }
        }
        require(success);
        return out[0] != 0;
    }
    /// Convenience method for a pairing check for two pairs.
    function pairingProd2(G1Point a1, G2Point a2, G1Point b1, G2Point b2) internal returns (bool) {
        G1Point[] memory p1 = new G1Point[](2);
        G2Point[] memory p2 = new G2Point[](2);
        p1[0] = a1;
        p1[1] = b1;
        p2[0] = a2;
        p2[1] = b2;
        return pairing(p1, p2);
    }
    /// Convenience method for a pairing check for three pairs.
    function pairingProd3(
            G1Point a1, G2Point a2,
            G1Point b1, G2Point b2,
            G1Point c1, G2Point c2
    ) internal returns (bool) {
        G1Point[] memory p1 = new G1Point[](3);
        G2Point[] memory p2 = new G2Point[](3);
        p1[0] = a1;
        p1[1] = b1;
        p1[2] = c1;
        p2[0] = a2;
        p2[1] = b2;
        p2[2] = c2;
        return pairing(p1, p2);
    }
    /// Convenience method for a pairing check for four pairs.
    function pairingProd4(
            G1Point a1, G2Point a2,
            G1Point b1, G2Point b2,
            G1Point c1, G2Point c2,
            G1Point d1, G2Point d2
    ) internal returns (bool) {
        G1Point[] memory p1 = new G1Point[](4);
        G2Point[] memory p2 = new G2Point[](4);
        p1[0] = a1;
        p1[1] = b1;
        p1[2] = c1;
        p1[3] = d1;
        p2[0] = a2;
        p2[1] = b2;
        p2[2] = c2;
        p2[3] = d2;
        return pairing(p1, p2);
    }
}
"#;
