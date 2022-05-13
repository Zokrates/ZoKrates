#[repr(C)]
pub struct Buffer {
    pub data: *const u8,
    pub length: i32,
}

#[repr(C)]
pub struct SetupResult {
    pub vk: Buffer,
    pub pk: Buffer,
}

#[repr(C)]
pub struct ProofResult {
    pub proof: Buffer,
}

extern "C" {
    pub fn c_free(ptr: *const u8);
}

impl Buffer {
    pub fn from_vec(v: &Vec<u8>) -> Buffer {
        let data = v.as_ptr();
        let len = v.len();

        Buffer {
            data,
            length: len as i32,
        }
    }
}
