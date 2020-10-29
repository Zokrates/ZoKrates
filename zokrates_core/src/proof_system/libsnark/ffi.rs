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
    pub fn from_vec(v: &Vec<u8>) -> Buffer {
        let mut buf = vec![0; v.len()].into_boxed_slice();
        buf.copy_from_slice(v.as_slice());

        let data = buf.as_mut_ptr();
        let len = buf.len();

        std::mem::forget(buf);

        Buffer {
            data,
            length: len as i32,
        }
    }

    pub unsafe fn drop(&self) {
        let s = std::slice::from_raw_parts_mut(self.data, self.length as usize);
        let s = s.as_mut_ptr();
        Box::from_raw(s);
    }

    /// The purpose of this function is to free memory allocated by C. Do not use otherwise.
    pub fn free(self) {
        unsafe { __free(self.data) };
    }
}
