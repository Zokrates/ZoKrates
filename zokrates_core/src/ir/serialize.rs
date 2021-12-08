use crate::ir::{Prog, ProgIterator, Statement};
use serde_cbor;
use std::io::{Read, Write};
use zokrates_field::*;

const ZOKRATES_MAGIC: &[u8; 4] = &[0x5a, 0x4f, 0x4b, 0];
const ZOKRATES_VERSION_1: &[u8; 4] = &[0, 0, 0, 1];

#[derive(PartialEq, Debug)]
pub enum ProgEnum<
    Bls12_381I: IntoIterator<Item = Statement<Bls12_381Field>>,
    Bn128I: IntoIterator<Item = Statement<Bn128Field>>,
    Bls12_377I: IntoIterator<Item = Statement<Bls12_377Field>>,
    Bw6_761I: IntoIterator<Item = Statement<Bw6_761Field>>,
> {
    Bls12_381Program(ProgIterator<Bls12_381Field, Bls12_381I>),
    Bn128Program(ProgIterator<Bn128Field, Bn128I>),
    Bls12_377Program(ProgIterator<Bls12_377Field, Bls12_377I>),
    Bw6_761Program(ProgIterator<Bw6_761Field, Bw6_761I>),
}

type MemoryProgEnum = ProgEnum<
    Vec<Statement<Bls12_381Field>>,
    Vec<Statement<Bn128Field>>,
    Vec<Statement<Bls12_377Field>>,
    Vec<Statement<Bw6_761Field>>,
>;

use serde::{Serialize, Serializer};
use std::cell::Cell;

impl<
        Bls12_381I: IntoIterator<Item = Statement<Bls12_381Field>>,
        Bn128I: IntoIterator<Item = Statement<Bn128Field>>,
        Bls12_377I: IntoIterator<Item = Statement<Bls12_377Field>>,
        Bw6_761I: IntoIterator<Item = Statement<Bw6_761Field>>,
    > ProgEnum<Bls12_381I, Bn128I, Bls12_377I, Bw6_761I>
{
    pub fn collect(self) -> MemoryProgEnum {
        match self {
            ProgEnum::Bls12_381Program(p) => ProgEnum::Bls12_381Program(p.collect()),
            ProgEnum::Bn128Program(p) => ProgEnum::Bn128Program(p.collect()),
            ProgEnum::Bls12_377Program(p) => ProgEnum::Bls12_377Program(p.collect()),
            ProgEnum::Bw6_761Program(p) => ProgEnum::Bw6_761Program(p.collect()),
        }
    }
}

pub fn write_as_cbor<T: Serialize + std::fmt::Debug, I, W>(
    out: &mut W,
    prog_iterator: ProgIterator<T, I>,
) -> serde_cbor::Result<()>
where
    I: IntoIterator<Item = Statement<T>>,
    W: Write,
{
    struct Wrapper<U>(Cell<Option<U>>);

    struct SerializableProgIterator<T: Serialize, I: IntoIterator<Item = Statement<T>>> {
        arguments: Vec<crate::flat_absy::FlatParameter>,
        return_count: usize,
        statements: Wrapper<I>,
    }

    impl<T, I> Serialize for SerializableProgIterator<T, I>
    where
        T: Serialize + std::fmt::Debug,
        I: IntoIterator<Item = Statement<T>>,
    {
        fn serialize<S: Serializer>(&self, s: S) -> Result<S::Ok, S::Error> {
            use serde::ser::SerializeStruct;

            let mut spi = s.serialize_struct("SerializableProgIterator", 3)?;
            spi.serialize_field("arguments", &self.arguments)?;
            spi.serialize_field("return_count", &self.return_count)?;
            spi.serialize_field("statements", &self.statements)?;
            spi.end()
        }
    }

    impl<I, P> Serialize for Wrapper<I>
    where
        I: IntoIterator<Item = P>,
        P: Serialize + std::fmt::Debug,
    {
        fn serialize<S: Serializer>(&self, s: S) -> Result<S::Ok, S::Error> {
            s.collect_seq(self.0.take().unwrap())
        }
    }

    serde_cbor::to_writer(
        out,
        &SerializableProgIterator {
            arguments: prog_iterator.arguments,
            return_count: prog_iterator.return_count,
            statements: Wrapper(Cell::new(Some(prog_iterator.statements))),
        },
    )
}

impl<T: Field, I: IntoIterator<Item = Statement<T>>> ProgIterator<T, I> {
    pub fn serialize<W: Write>(self, mut w: W) {
        w.write_all(ZOKRATES_MAGIC).unwrap();
        w.write_all(ZOKRATES_VERSION_1).unwrap();
        w.write_all(&T::id()).unwrap();

        write_as_cbor(&mut w, self).unwrap();
    }
}

impl
    ProgEnum<
        std::vec::IntoIter<Statement<Bls12_381Field>>,
        std::vec::IntoIter<Statement<Bn128Field>>,
        std::vec::IntoIter<Statement<Bls12_377Field>>,
        std::vec::IntoIter<Statement<Bw6_761Field>>,
    >
{
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
                    m if m == Bls12_381Field::id() => {
                        let p: Prog<Bls12_381Field> = serde_cbor::from_reader(r).unwrap();

                        Ok(ProgEnum::Bls12_381Program(ProgIterator {
                            statements: p.statements.into_iter(),
                            arguments: p.arguments,
                            return_count: p.return_count,
                        }))
                    }
                    m if m == Bn128Field::id() => {
                        let p: Prog<Bn128Field> = serde_cbor::from_reader(r).unwrap();

                        Ok(ProgEnum::Bn128Program(ProgIterator {
                            statements: p.statements.into_iter(),
                            arguments: p.arguments,
                            return_count: p.return_count,
                        }))
                    }
                    m if m == Bls12_377Field::id() => {
                        let p: Prog<Bls12_377Field> = serde_cbor::from_reader(r).unwrap();

                        Ok(ProgEnum::Bls12_377Program(ProgIterator {
                            statements: p.statements.into_iter(),
                            arguments: p.arguments,
                            return_count: p.return_count,
                        }))
                    }
                    m if m == Bw6_761Field::id() => {
                        let p: Prog<Bw6_761Field> = serde_cbor::from_reader(r).unwrap();

                        Ok(ProgEnum::Bw6_761Program(ProgIterator {
                            statements: p.statements.into_iter(),
                            arguments: p.arguments,
                            return_count: p.return_count,
                        }))
                    }
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
        let p: ir::Prog<Bn128Field> = ir::Prog::default();

        let mut buffer = Cursor::new(vec![]);
        p.clone().serialize(&mut buffer);

        // rewind back to the beginning of the file
        buffer.seek(SeekFrom::Start(0)).unwrap();

        // deserialize
        let deserialized_p = ProgEnum::deserialize(buffer).unwrap();

        assert_eq!(ProgEnum::Bn128Program(p), deserialized_p.collect());

        let p: ir::Prog<Bls12_381Field> = ir::Prog::default();

        let mut buffer = Cursor::new(vec![]);
        p.clone().serialize(&mut buffer);

        // rewind back to the beginning of the file
        buffer.seek(SeekFrom::Start(0)).unwrap();

        // deserialize
        let deserialized_p = ProgEnum::deserialize(buffer).unwrap();

        assert_eq!(ProgEnum::Bls12_381Program(p), deserialized_p.collect());
    }
}
