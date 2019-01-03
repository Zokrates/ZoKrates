extern crate zokrates_field;
extern crate num;
use zokrates_field::field::{Field, FieldPrime};
use num::{Zero, One};

static INPUT_BUFFER : [u8;32] = [0u8;32];
static mut OUTPUT_BUFFER : [u8;64] = [0u8;64];

#[no_mangle]
pub extern "C" fn get_inputs_off() -> *const u8 {
    return &INPUT_BUFFER as *const u8;
}

#[no_mangle]
pub unsafe extern "C" fn solve() -> *const u8 {
    // Transform the input bytes into output
    let input = FieldPrime::from_byte_vector(Vec::from(&INPUT_BUFFER[..]));

    let (output0, output1) = if input.is_zero() {
        (FieldPrime::zero(), FieldPrime::one())
    } else {
        (FieldPrime::one(), FieldPrime::one() / input)
    };

    // Transform outputs back into bytes
    &OUTPUT_BUFFER[..32].copy_from_slice(&output0.into_byte_vector()[..]);
    &OUTPUT_BUFFER[32..].copy_from_slice(&output1.into_byte_vector()[..]);
    
    return &OUTPUT_BUFFER as *const u8;
}

fn main() {
}
