use crate::flat_absy::FlatVariable;
use std::collections::{BTreeMap, HashMap};
use std::fmt;
use std::io;
use std::io::{Read, Write};
use zokrates_field::Field;

#[derive(Clone, Debug, PartialEq)]
pub struct Witness<T>(pub BTreeMap<FlatVariable, T>);

impl<T: Field> Witness<T> {
    pub fn return_values(&self) -> Vec<T> {
        let out = self
            .0
            .iter()
            .filter(|(k, _)| k.is_output())
            .collect::<HashMap<_, _>>();

        (0..out.len())
            .map(|i| *out.get(&FlatVariable::public(i)).unwrap())
            .cloned()
            .collect()
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

    pub fn write<W: Write>(&self, writer: W) -> io::Result<()> {
        let mut wtr = csv::WriterBuilder::new()
            .delimiter(b' ')
            .flexible(true)
            .has_headers(false)
            .from_writer(writer);

        // Write each line of the witness to the file
        for (variable, value) in &self.0 {
            wtr.serialize((variable.to_string(), value.to_dec_string()))?;
        }

        Ok(())
    }

    pub fn read<R: Read>(mut reader: R) -> io::Result<Self> {
        let mut rdr = csv::ReaderBuilder::new()
            .delimiter(b' ')
            .flexible(true)
            .has_headers(false)
            .from_reader(&mut reader);

        let map = rdr
            .deserialize::<(String, String)>()
            .map(|r| {
                r.map(|(variable, value)| {
                    let variable =
                        FlatVariable::try_from_human_readable(&variable).map_err(|why| {
                            io::Error::new(
                                io::ErrorKind::Other,
                                format!("Invalid variable in witness: {}", why),
                            )
                        })?;
                    let value = T::try_from_dec_str(&value).map_err(|_| {
                        io::Error::new(
                            io::ErrorKind::Other,
                            format!("Invalid value in witness: {}", value),
                        )
                    })?;
                    Ok((variable, value))
                })
                .map_err(|e| match e.into_kind() {
                    csv::ErrorKind::Io(e) => e,
                    e => io::Error::new(io::ErrorKind::Other, format!("{:?}", e)),
                })?
            })
            .collect::<io::Result<BTreeMap<FlatVariable, T>>>()?;

        Ok(Witness(map))
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
                    (FlatVariable::new(42), Bn128Field::from(42)),
                    (FlatVariable::public(8), Bn128Field::from(8)),
                    (FlatVariable::one(), Bn128Field::from(1)),
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
        fn wrong_value() {
            let mut buff = Cursor::new(vec![]);

            buff.write_all("_1 123bug".as_ref()).unwrap();
            buff.set_position(0);

            assert!(Witness::<Bn128Field>::read(buff).is_err());
        }

        #[test]
        fn wrong_variable() {
            let mut buff = Cursor::new(vec![]);

            buff.write_all("_1bug 123".as_ref()).unwrap();
            buff.set_position(0);

            assert!(Witness::<Bn128Field>::read(buff).is_err());
        }

        #[test]
        fn not_csv() {
            let mut buff = Cursor::new(vec![]);
            buff.write_all("whatwhat".as_ref()).unwrap();
            buff.set_position(0);

            assert!(Witness::<Bn128Field>::read(buff).is_err());
        }
    }
}
