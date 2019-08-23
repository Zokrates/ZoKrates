mod rust;
#[cfg(feature = "wasm")]
mod wasm;

pub use self::rust::RustHelper;
#[cfg(feature = "wasm")]
pub use self::wasm::WasmHelper;
use std::fmt;
use zokrates_field::field::Field;

#[derive(Clone, PartialEq, Debug, Serialize, Deserialize)]
pub enum Helper {
    Rust(RustHelper),
    #[cfg(feature = "wasm")]
    Wasm(WasmHelper),
}

#[cfg(feature = "wasm")]
impl Helper {
    pub fn identity() -> Self {
        Helper::Wasm(WasmHelper::from_hex(WasmHelper::IDENTITY_WASM))
    }

    pub fn bits() -> Self {
        Helper::Wasm(WasmHelper::from(WasmHelper::BITS_WASM))
    }
}

#[cfg(not(feature = "wasm"))]
impl Helper {
    pub fn identity() -> Self {
        Helper::Rust(RustHelper::Identity)
    }

    pub fn bits() -> Self {
        Helper::Rust(RustHelper::Bits)
    }
}

impl fmt::Display for Helper {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Helper::Rust(ref h) => write!(f, "Rust::{}", h),
            #[cfg(feature = "wasm")]
            Helper::Wasm(ref h) => write!(f, "Wasm::{}", h),
        }
    }
}

pub trait Executable<T: Field>: Signed {
    fn execute(&self, inputs: &Vec<T>) -> Result<Vec<T>, String>;
}

pub trait Signed {
    fn get_signature(&self) -> (usize, usize);
}

impl<T: Field> Executable<T> for Helper {
    fn execute(&self, inputs: &Vec<T>) -> Result<Vec<T>, String> {
        let (expected_input_count, expected_output_count) = self.get_signature();
        assert!(inputs.len() == expected_input_count);

        let result = match self {
            Helper::Rust(helper) => helper.execute(inputs),
            #[cfg(feature = "wasm")]
            Helper::Wasm(helper) => helper.execute(inputs),
        };

        match result {
            Ok(ref r) if r.len() != expected_output_count => Err(format!(
                "invalid witness size: is {} but should be {}",
                r.len(),
                expected_output_count
            )
            .to_string()),
            r => r,
        }
    }
}

impl Signed for Helper {
    fn get_signature(&self) -> (usize, usize) {
        match self {
            Helper::Rust(helper) => helper.get_signature(),
            #[cfg(feature = "wasm")]
            Helper::Wasm(helper) => helper.get_signature(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use zokrates_field::field::FieldPrime;

    mod eq_condition {

        // Wanted: (Y = (X != 0) ? 1 : 0)
        // # Y = if X == 0 then 0 else 1 fi
        // # M = if X == 0 then 1 else 1/X fi

        use super::*;

        #[test]
        fn execute() {
            let cond_eq = RustHelper::ConditionEq;
            let inputs = vec![0];
            let r = cond_eq
                .execute(&inputs.iter().map(|&i| FieldPrime::from(i)).collect())
                .unwrap();
            let res: Vec<FieldPrime> = vec![0, 1].iter().map(|&i| FieldPrime::from(i)).collect();
            assert_eq!(r, &res[..]);
        }

        #[test]
        fn execute_non_eq() {
            let cond_eq = RustHelper::ConditionEq;
            let inputs = vec![1];
            let r = cond_eq
                .execute(&inputs.iter().map(|&i| FieldPrime::from(i)).collect())
                .unwrap();
            let res: Vec<FieldPrime> = vec![1, 1].iter().map(|&i| FieldPrime::from(i)).collect();
            assert_eq!(r, &res[..]);
        }
    }
}
