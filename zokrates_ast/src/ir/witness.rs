use crate::common::flat::Variable;
use std::collections::{BTreeMap, HashMap};
use std::fmt;
use std::io;
use std::io::{Read, Write};
use zokrates_field::Field;

#[derive(Clone, Debug, PartialEq, Eq, Default)]
pub struct Witness<T>(pub BTreeMap<Variable, T>);

impl<T: Field> Witness<T> {
    pub fn return_values(&self) -> Vec<T> {
        let out = self
            .0
            .iter()
            .filter(|(k, _)| k.is_output())
            .collect::<HashMap<_, _>>();

        (0..out.len())
            .map(|i| *out.get(&Variable::public(i)).unwrap())
            .cloned()
            .collect()
    }

    pub fn insert(&mut self, var: Variable, val: T) -> Option<T> {
        self.0.insert(var, val)
    }

    pub fn format_outputs(&self) -> String {
        self.0
            .iter()
            .filter_map(|(variable, value)| match variable {
                variable if variable.is_output() => Some(format!("{} {}", variable, value)),
                _ => None,
            })
            .collect::<Vec<String>>()
            .join("\n")
    }

    pub fn empty() -> Self {
        Witness(BTreeMap::new())
    }

    pub fn write<W: Write>(&self, mut writer: W) -> io::Result<()> {
        let length = self.0.len();
        writer.write_all(&length.to_le_bytes())?;

        for (variable, value) in &self.0 {
            variable.write(&mut writer)?;
            value.write(&mut writer)?;
        }
        Ok(())
    }

    pub fn read<R: Read>(mut reader: R) -> io::Result<Self> {
        let mut witness = Self::empty();

        let mut buf = [0; std::mem::size_of::<usize>()];
        reader.read_exact(&mut buf)?;

        let length: usize = usize::from_le_bytes(buf);

        for _ in 0..length {
            let var = Variable::read(&mut reader)?;
            let val = T::read(&mut reader)?;

            witness.insert(var, val);
        }

        Ok(witness)
    }

    pub fn write_json<W: Write>(&self, writer: W) -> io::Result<()> {
        let map = self
            .0
            .iter()
            .map(|(k, v)| (k.to_string(), serde_json::json!(v.to_dec_string())))
            .collect::<serde_json::Map<String, serde_json::Value>>();

        serde_json::to_writer_pretty(writer, &map)?;
        Ok(())
    }
}

impl<T: Field> fmt::Display for Witness<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "{}",
            self.0
                .iter()
                .map(|(k, v)| format!("{} {}", k, v.to_dec_string()))
                .collect::<Vec<_>>()
                .join("\n")
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use zokrates_field::Bn128Field;

    mod io {
        use super::*;
        use std::io::Cursor;

        #[test]
        fn serialize_deserialize() {
            let w = Witness(
                vec![
                    (Variable::new(42), Bn128Field::from(42)),
                    (Variable::public(8), Bn128Field::from(8)),
                    (Variable::one(), Bn128Field::from(1)),
                ]
                .into_iter()
                .collect(),
            );

            let mut buff = Cursor::new(vec![]);

            w.write(&mut buff).unwrap();
            buff.set_position(0);

            let r = Witness::read(buff).unwrap();

            assert_eq!(w, r);
        }

        #[test]
        fn serialize_json() {
            let w = Witness(
                vec![
                    (Variable::new(42), Bn128Field::from(42)),
                    (Variable::public(8), Bn128Field::from(8)),
                    (Variable::one(), Bn128Field::from(1)),
                ]
                .into_iter()
                .collect(),
            );

            let mut buf = Cursor::new(vec![]);
            w.write_json(&mut buf).unwrap();

            let output = String::from_utf8(buf.into_inner()).unwrap();
            assert_eq!(
                output.as_str(),
                r#"{
  "~out_8": "8",
  "~one": "1",
  "_42": "42"
}"#
            )
        }
    }
}
