#[repr(C)]
pub struct Buffer {
    pub data: *mut u8,
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
    fn __free(ptr: *mut u8);
}

impl Buffer {
    pub fn from_vec(v: &mut Vec<u8>) -> Buffer {
        let length = v.len() as i32;
        Buffer {
            data: v.as_mut_ptr(),
            length,
        }
    }

    /// The purpose of this function is to free memory previously allocated by "malloc"
    /// from C standard library. Do not use otherwise.
    pub fn free(self) {
        unsafe { __free(self.data) };
    }
}
