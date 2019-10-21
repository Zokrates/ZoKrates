use bincode::{deserialize_from, serialize_into, Infinite};
use ir::Prog;
use std::io::{Read, Write};
use zokrates_field::*;

const ZOKRATES_MAGIC: &[u8; 4] = &[0x5a, 0x4f, 0x4b, 0];
const ZOKRATES_VERSION_1: &[u8; 4] = &[0, 0, 0, 1];

pub enum ProgEnum {
    Bls12Program(Prog<Bls12Field>),
    Bn128Program(Prog<Bn128Field>),
}

impl<T: Field> Prog<T> {
    pub fn serialize<W: Write>(&self, mut w: W) {
        w.write(ZOKRATES_MAGIC).unwrap();
        w.write(ZOKRATES_VERSION_1).unwrap();
        w.write(&T::id()).unwrap();

        serialize_into(&mut w, self, Infinite)
            .map_err(|_| "Unable to write data to file.".to_string())
            .unwrap();
    }
}

impl ProgEnum {
    pub fn deserialize<R: Read>(mut r: R) -> Result<Self, ()> {
        // Check the magic number, `ZOK`
        let mut magic = [0; 4];
        r.read_exact(&mut magic).unwrap();

        assert_eq!(&magic, ZOKRATES_MAGIC);

        // Check the version, 1
        let mut version = [0; 4];
        r.read_exact(&mut version).unwrap();

        assert_eq!(&version, ZOKRATES_VERSION_1);

        // Check the curve identifier, deserializing accordingly
        let mut curve = [0; 4];
        r.read_exact(&mut curve).unwrap();

        match curve {
            m if m == Bls12Field::id() => Ok(ProgEnum::Bls12Program(
                deserialize_from(&mut r, Infinite).unwrap(),
            )),
            m if m == Bn128Field::id() => Ok(ProgEnum::Bn128Program(
                deserialize_from(&mut r, Infinite).unwrap(),
            )),
            _ => Err(()),
        }
    }
}
