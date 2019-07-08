mod rust;
#[cfg(feature = "wasm")]
mod wasm;

pub use self::rust::RustHelper;
#[cfg(feature = "wasm")]
pub use self::wasm::WasmHelper;
use crate::flat_absy::{FlatExpression, FlatVariable};
use std::fmt;
use zokrates_field::Field;

#[derive(Clone, PartialEq, Serialize, Deserialize)]
pub struct DirectiveStatement<T> {
    pub inputs: Vec<FlatExpression<T>>,
    pub outputs: Vec<FlatVariable>,
    pub helper: Helper,
}

impl<T: fmt::Debug + fmt::Display> fmt::Debug for DirectiveStatement<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        unimplemented!()
    }
}

impl<T> DirectiveStatement<T> {
    pub fn new<E: Into<FlatExpression<T>>>(
        outputs: Vec<FlatVariable>,
        helper: Helper,
        inputs: Vec<E>,
    ) -> Self {
        let (in_len, out_len) = helper.get_signature();
        assert_eq!(in_len, inputs.len());
        assert_eq!(out_len, outputs.len());
        DirectiveStatement {
            helper,
            inputs: inputs.into_iter().map(|i| i.into()).collect(),
            outputs,
        }
    }
}

impl<T: fmt::Display + fmt::Debug> fmt::Display for DirectiveStatement<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "# {} = {}({})",
            self.outputs
                .iter()
                .map(|o| o.to_string())
                .collect::<Vec<String>>()
                .join(", "),
            self.helper,
            self.inputs
                .iter()
                .map(|i| i.to_string())
                .collect::<Vec<String>>()
                .join(", ")
        )
    }
}

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
    use zokrates_field::Bn128Field;

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
