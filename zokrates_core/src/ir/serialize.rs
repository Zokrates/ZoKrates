use crate::ir::Prog;
use bincode::{deserialize_from, serialize_into, Infinite};
use std::io::{Read, Write};
use zokrates_field::*;

const ZOKRATES_MAGIC: &[u8; 4] = &[0x5a, 0x4f, 0x4b, 0];
const ZOKRATES_VERSION_1: &[u8; 4] = &[0, 0, 0, 1];

#[derive(PartialEq, Debug)]
pub enum ProgEnum {
    Bls12_381Program(Prog<Bls12_381Field>),
    Bn128Program(Prog<Bn128Field>),
    Bls12_377Program(Prog<Bls12_377Field>),
    Bw6_761Program(Prog<Bw6_761Field>),
}

impl<T: Field> Prog<T> {
    pub fn serialize<W: Write>(&self, mut w: W) {
        w.write_all(ZOKRATES_MAGIC).unwrap();
        w.write_all(ZOKRATES_VERSION_1).unwrap();
        w.write_all(&T::id()).unwrap();

        serialize_into(&mut w, self, Infinite).unwrap();
    }
}

impl ProgEnum {
    pub fn deserialize<R: Read>(mut r: R) -> Result<Self, String> {
        // Check the magic number, `ZOK`
        let mut magic = [0; 4];
        r.read_exact(&mut magic)
            .map_err(|_| String::from("Cannot read magic number"))?;

        if &magic == ZOKRATES_MAGIC {
            // Check the version, 1
            let mut version = [0; 4];
            r.read_exact(&mut version)
                .map_err(|_| String::from("Cannot read version"))?;

            if &version == ZOKRATES_VERSION_1 {
                // Check the curve identifier, deserializing accordingly
                let mut curve = [0; 4];
                r.read_exact(&mut curve)
                    .map_err(|_| String::from("Cannot read curve identifier"))?;

                match curve {
                    m if m == Bls12_381Field::id() => Ok(ProgEnum::Bls12_381Program(
                        deserialize_from(&mut r, Infinite).unwrap(),
                    )),
                    m if m == Bn128Field::id() => Ok(ProgEnum::Bn128Program(
                        deserialize_from(&mut r, Infinite).unwrap(),
                    )),
                    m if m == Bls12_377Field::id() => Ok(ProgEnum::Bls12_377Program(
                        deserialize_from(&mut r, Infinite).unwrap(),
                    )),
                    m if m == Bw6_761Field::id() => Ok(ProgEnum::Bw6_761Program(
                        deserialize_from(&mut r, Infinite).unwrap(),
                    )),
                    _ => Err(String::from("Unknown curve identifier")),
                }
            } else {
                Err(String::from("Unknown version"))
            }
        } else {
            Err(String::from("Wrong magic number"))
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir;
    use std::io::{Cursor, Seek, SeekFrom};
    use zokrates_field::{Bls12_381Field, Bn128Field};

    #[test]
    fn ser_deser_v1() {
        let p: ir::Prog<Bn128Field> = ir::Prog {
            main: ir::Function {
                arguments: vec![],
                id: "something".to_string(),
                returns: vec![],
                statements: vec![],
            },
            private: vec![],
        };

        let mut buffer = Cursor::new(vec![]);
        p.serialize(&mut buffer);

        // rewind back to the beginning of the file
        buffer.seek(SeekFrom::Start(0)).unwrap();

        // deserialize
        let deserialized_p = ProgEnum::deserialize(buffer).unwrap();

        assert_eq!(ProgEnum::Bn128Program(p), deserialized_p);

        let p: ir::Prog<Bls12_381Field> = ir::Prog {
            main: ir::Function {
                arguments: vec![],
                id: "something".to_string(),
                returns: vec![],
                statements: vec![],
            },
            private: vec![],
        };

        let mut buffer = Cursor::new(vec![]);
        p.serialize(&mut buffer);

        // rewind back to the beginning of the file
        buffer.seek(SeekFrom::Start(0)).unwrap();

        // deserialize
        let deserialized_p = ProgEnum::deserialize(buffer).unwrap();

        assert_eq!(ProgEnum::Bls12_381Program(p), deserialized_p);
    }
}
