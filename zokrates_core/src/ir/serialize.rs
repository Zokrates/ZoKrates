use crate::ir::{ProgIterator, Statement};
use serde_cbor::{self, StreamDeserializer};
use std::io::{Read, Write};
use zokrates_field::*;

const ZOKRATES_MAGIC: &[u8; 4] = &[0x5a, 0x4f, 0x4b, 0];
const ZOKRATES_VERSION_2: &[u8; 4] = &[0, 0, 0, 2];

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

// pub fn _write_as_cbor<T: Serialize + std::fmt::Debug, I, W>(
//     out: &mut W,
//     prog_iterator: ProgIterator<T, I>,
// ) -> serde_cbor::Result<()>
// where
//     I: IntoIterator<Item = Statement<T>>,
//     W: Write,
// {
//     struct Wrapper<U>(Cell<Option<U>>);

//     struct SerializableProgIterator<T: Serialize, I: IntoIterator<Item = crate::ir::Statement<T>>> {
//         arguments: Vec<crate::flat_absy::FlatParameter>,
//         return_count: usize,
//         statements: Wrapper<I>,
//     }

//     impl<T, I> Serialize for SerializableProgIterator<T, I>
//     where
//         T: Serialize + std::fmt::Debug,
//         I: IntoIterator<Item = crate::ir::Statement<T>>,
//     {
//         fn serialize<S: Serializer>(&self, s: S) -> Result<S::Ok, S::Error> {
//             use serde::ser::SerializeStruct;

//             let mut spi = s.serialize_struct("SerializableProgIterator", 3)?;
//             spi.serialize_field("arguments", &self.arguments)?;
//             spi.serialize_field("return_count", &self.return_count)?;
//             spi.serialize_field("statements", &self.statements)?;
//             spi.end()
//         }
//     }

//     impl<I, P> Serialize for Wrapper<I>
//     where
//         I: IntoIterator<Item = P>,
//         P: Serialize + std::fmt::Debug,
//     {
//         fn serialize<S: Serializer>(&self, s: S) -> Result<S::Ok, S::Error> {
//             s.collect_seq(self.0.take().unwrap())
//         }
//     }

//     serde_cbor::to_writer(
//         out,
//         &SerializableProgIterator {
//             arguments: prog_iterator.arguments,
//             return_count: prog_iterator.return_count,
//             statements: Wrapper(Cell::new(Some(prog_iterator.statements))),
//         },
//     )
// }

impl<T: Field, I: IntoIterator<Item = Statement<T>>> ProgIterator<T, I> {
    pub fn serialize<W: Write>(self, mut w: W) {
        w.write_all(ZOKRATES_MAGIC).unwrap();
        w.write_all(ZOKRATES_VERSION_2).unwrap();
        w.write_all(&T::id()).unwrap();

        serde_cbor::to_writer(&mut w, &self.arguments).unwrap();
        serde_cbor::to_writer(&mut w, &self.return_count).unwrap();
        for s in self.statements {
            serde_cbor::to_writer(&mut w, &s).unwrap();
        }
    }
}

pub struct UnwrappedStreamDeserializer<'de, R, T> {
    s: StreamDeserializer<'de, R, T>,
}

impl<'de, R: serde_cbor::de::Read<'de>, T: serde::Deserialize<'de>> Iterator
    for UnwrappedStreamDeserializer<'de, R, T>
{
    type Item = T;

    fn next(&mut self) -> Option<T> {
        self.s.next().transpose().unwrap()
    }
}

impl<'de, R: Read>
    ProgEnum<
        UnwrappedStreamDeserializer<'de, serde_cbor::de::IoRead<R>, Statement<Bls12_381Field>>,
        UnwrappedStreamDeserializer<'de, serde_cbor::de::IoRead<R>, Statement<Bn128Field>>,
        UnwrappedStreamDeserializer<'de, serde_cbor::de::IoRead<R>, Statement<Bls12_377Field>>,
        UnwrappedStreamDeserializer<'de, serde_cbor::de::IoRead<R>, Statement<Bw6_761Field>>,
    >
{
    pub fn deserialize(mut r: R) -> Result<Self, String> {
        // Check the magic number, `ZOK`
        let mut magic = [0; 4];
        r.read_exact(&mut magic)
            .map_err(|_| String::from("Cannot read magic number"))?;

        if &magic == ZOKRATES_MAGIC {
            // Check the version, 2
            let mut version = [0; 4];
            r.read_exact(&mut version)
                .map_err(|_| String::from("Cannot read version"))?;

            if &version == ZOKRATES_VERSION_2 {
                // Check the curve identifier, deserializing accordingly
                let mut curve = [0; 4];
                r.read_exact(&mut curve)
                    .map_err(|_| String::from("Cannot read curve identifier"))?;

                use serde::de::Deserializer;
                let mut p = serde_cbor::Deserializer::from_reader(r);

                struct ArgumentsVisitor;

                impl<'de> serde::de::Visitor<'de> for ArgumentsVisitor {
                    type Value = Vec<crate::ir::FlatParameter>;
                    fn expecting(&self, formatter: &mut std::fmt::Formatter) -> std::fmt::Result {
                        formatter.write_str("seq of flat param")
                    }

                    fn visit_seq<A>(self, mut seq: A) -> Result<Self::Value, A::Error>
                    where
                        A: serde::de::SeqAccess<'de>,
                    {
                        let mut res = vec![];
                        while let Some(e) = seq.next_element().unwrap() {
                            res.push(dbg!(e));
                        }
                        Ok(res)
                    }
                }

                let arguments = p.deserialize_seq(ArgumentsVisitor).unwrap();

                struct ReturnCountVisitor;

                impl<'de> serde::de::Visitor<'de> for ReturnCountVisitor {
                    type Value = usize;
                    fn expecting(&self, formatter: &mut std::fmt::Formatter) -> std::fmt::Result {
                        formatter.write_str("usize")
                    }

                    fn visit_u32<E>(self, v: u32) -> Result<Self::Value, E>
                    where
                        E: serde::de::Error,
                    {
                        Ok(v as usize)
                    }

                    fn visit_u8<E>(self, v: u8) -> Result<Self::Value, E>
                    where
                        E: serde::de::Error,
                    {
                        Ok(v as usize)
                    }

                    fn visit_u16<E>(self, v: u16) -> Result<Self::Value, E>
                    where
                        E: serde::de::Error,
                    {
                        Ok(v as usize)
                    }
                }

                let return_count = p.deserialize_u32(ReturnCountVisitor).unwrap();

                match curve {
                    m if m == Bls12_381Field::id() => {
                        let s = p.into_iter::<Statement<Bls12_381Field>>();

                        Ok(ProgEnum::Bls12_381Program(ProgIterator {
                            arguments,
                            return_count,
                            statements: UnwrappedStreamDeserializer { s },
                        }))
                    }
                    m if m == Bn128Field::id() => {
                        let s = p.into_iter::<Statement<Bn128Field>>();

                        Ok(ProgEnum::Bn128Program(ProgIterator {
                            arguments,
                            return_count,
                            statements: UnwrappedStreamDeserializer { s },
                        }))
                    }
                    m if m == Bls12_377Field::id() => {
                        let s = p.into_iter::<Statement<Bls12_377Field>>();

                        Ok(ProgEnum::Bls12_377Program(ProgIterator {
                            arguments,
                            return_count,
                            statements: UnwrappedStreamDeserializer { s },
                        }))
                    }
                    m if m == Bw6_761Field::id() => {
                        let s = p.into_iter::<Statement<Bw6_761Field>>();

                        Ok(ProgEnum::Bw6_761Program(ProgIterator {
                            arguments,
                            return_count,
                            statements: UnwrappedStreamDeserializer { s },
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
    fn ser_deser_v2() {
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
