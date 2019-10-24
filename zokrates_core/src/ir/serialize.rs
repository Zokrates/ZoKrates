use bincode::{deserialize_from, serialize_into, Infinite};
use ir::Prog;
use std::io::{Read, Write};
use zokrates_field::*;

const ZOKRATES_MAGIC: &[u8; 4] = &[0x5a, 0x4f, 0x4b, 0];
const ZOKRATES_VERSION_1: &[u8; 4] = &[0, 0, 0, 1];

#[derive(PartialEq, Debug)]
pub enum ProgEnum {
    Bls12Program(Prog<Bls12Field>),
    Bn128Program(Prog<Bn128Field>),
}

impl<T: Field> Prog<T> {
    pub fn serialize<W: Write>(&self, mut w: W) {
        w.write(ZOKRATES_MAGIC).unwrap();
        w.write(ZOKRATES_VERSION_1).unwrap();
        w.write(&T::id()).unwrap();

        serialize_into(&mut w, self, Infinite).unwrap();
    }
}

impl ProgEnum {
    pub fn deserialize<R: Read>(mut r: R) -> Result<Self, ()> {
        // Check the magic number, `ZOK`
        let mut magic = [0; 4];
        r.read_exact(&mut magic).map_err(|_| ())?;

        if &magic == ZOKRATES_MAGIC {
            // Check the version, 1
            let mut version = [0; 4];
            r.read_exact(&mut version).map_err(|_| ())?;

            if &version == ZOKRATES_VERSION_1 {
                // Check the curve identifier, deserializing accordingly
                let mut curve = [0; 4];
                r.read_exact(&mut curve).map_err(|_| ())?;

                match curve {
                    m if m == Bls12Field::id() => Ok(ProgEnum::Bls12Program(
                        deserialize_from(&mut r, Infinite).unwrap(),
                    )),
                    m if m == Bn128Field::id() => Ok(ProgEnum::Bn128Program(
                        deserialize_from(&mut r, Infinite).unwrap(),
                    )),
                    _ => Err(()),
                }
            } else {
                Err(())
            }
        } else {
            Err(())
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ir;
    use std::io::{Cursor, Seek, SeekFrom};
    use typed_absy::types::Signature;
    use zokrates_field::{Bls12Field, Bn128Field};

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
            signature: Signature::new(),
        };

        let mut buffer = Cursor::new(vec![]);
        p.serialize(&mut buffer);

        // rewind back to the beginning of the file
        buffer.seek(SeekFrom::Start(0)).unwrap();

        // deserialize
        let deserialized_p = ProgEnum::deserialize(buffer).unwrap();

        assert_eq!(ProgEnum::Bn128Program(p), deserialized_p);

        let p: ir::Prog<Bls12Field> = ir::Prog {
            main: ir::Function {
                arguments: vec![],
                id: "something".to_string(),
                returns: vec![],
                statements: vec![],
            },
            private: vec![],
            signature: Signature::new(),
        };

        let mut buffer = Cursor::new(vec![]);
        p.serialize(&mut buffer);

        // rewind back to the beginning of the file
        buffer.seek(SeekFrom::Start(0)).unwrap();

        // deserialize
        let deserialized_p = ProgEnum::deserialize(buffer).unwrap();

        assert_eq!(ProgEnum::Bls12Program(p), deserialized_p);
    }
}
