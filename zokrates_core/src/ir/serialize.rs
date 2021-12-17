use crate::ir::{DynamicError, IntoStatements, Ir, MemoryIrStatements, ProgIterator, Statement};
use fallible_iterator::FallibleIterator;
use serde_cbor::{self, StreamDeserializer};
use std::io::{Read, Write};
use zokrates_field::*;

const ZOKRATES_MAGIC: &[u8; 4] = &[0x5a, 0x4f, 0x4b, 0];
const ZOKRATES_VERSION_2: &[u8; 4] = &[0, 0, 0, 2];

#[derive(PartialEq, Debug)]
pub enum ProgEnum<
    Bls12_381I: IntoStatements<Ir<Bls12_381Field>>,
    Bn128I: IntoStatements<Ir<Bn128Field>>,
    Bls12_377I: IntoStatements<Ir<Bls12_377Field>>,
    Bw6_761I: IntoStatements<Ir<Bw6_761Field>>,
> {
    Bls12_381Program(ProgIterator<Bls12_381Field, Bls12_381I>),
    Bn128Program(ProgIterator<Bn128Field, Bn128I>),
    Bls12_377Program(ProgIterator<Bls12_377Field, Bls12_377I>),
    Bw6_761Program(ProgIterator<Bw6_761Field, Bw6_761I>),
}

type MemoryProgEnum = ProgEnum<
    MemoryIrStatements<Bls12_381Field>,
    MemoryIrStatements<Bn128Field>,
    MemoryIrStatements<Bls12_377Field>,
    MemoryIrStatements<Bw6_761Field>,
>;

impl<
        Bls12_381I: IntoStatements<Ir<Bls12_381Field>>,
        Bn128I: IntoStatements<Ir<Bn128Field>>,
        Bls12_377I: IntoStatements<Ir<Bls12_377Field>>,
        Bw6_761I: IntoStatements<Ir<Bw6_761Field>>,
    > ProgEnum<Bls12_381I, Bn128I, Bls12_377I, Bw6_761I>
{
    pub fn collect(self) -> Result<MemoryProgEnum, DynamicError> {
        Ok(match self {
            ProgEnum::Bls12_381Program(p) => ProgEnum::Bls12_381Program(p.collect()?),
            ProgEnum::Bn128Program(p) => ProgEnum::Bn128Program(p.collect()?),
            ProgEnum::Bls12_377Program(p) => ProgEnum::Bls12_377Program(p.collect()?),
            ProgEnum::Bw6_761Program(p) => ProgEnum::Bw6_761Program(p.collect()?),
        })
    }
}

impl<T: Field, I: IntoStatements<Ir<T>>> ProgIterator<T, I> {
    /// serialize a program iterator, returning the number of constraints serialized
    /// Note that we only return constraints, not other statements such as directives
    pub fn serialize<W: Write>(self, mut w: W) -> Result<usize, DynamicError> {
        w.write_all(ZOKRATES_MAGIC)?;
        w.write_all(ZOKRATES_VERSION_2)?;
        w.write_all(&T::id())?;

        serde_cbor::to_writer(&mut w, &self.arguments)?;
        serde_cbor::to_writer(&mut w, &self.return_count)?;

        let mut statements = self.statements.into_fallible_iter();

        let mut count = 0;
        while let Some(s) = statements.next()? {
            if matches!(s, Statement::Constraint(..)) {
                count += 1;
            }
            serde_cbor::to_writer(&mut w, &s)?;
        }

        Ok(count)
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

impl<'de, R: serde_cbor::de::Read<'de>, T: serde::Deserialize<'de>> FallibleIterator
    for UnwrappedStreamDeserializer<'de, R, T>
{
    type Item = T;
    type Error = DynamicError;

    fn next(&mut self) -> Result<Option<T>, Self::Error> {
        self.s.next().transpose().map_err(|e| e.into())
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
                            res.push(e);
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

                        Ok(ProgEnum::Bls12_381Program(ProgIterator::new(
                            arguments,
                            UnwrappedStreamDeserializer { s },
                            return_count,
                        )))
                    }
                    m if m == Bn128Field::id() => {
                        let s = p.into_iter::<Statement<Bn128Field>>();

                        Ok(ProgEnum::Bn128Program(ProgIterator::new(
                            arguments,
                            UnwrappedStreamDeserializer { s },
                            return_count,
                        )))
                    }
                    m if m == Bls12_377Field::id() => {
                        let s = p.into_iter::<Statement<Bls12_377Field>>();

                        Ok(ProgEnum::Bls12_377Program(ProgIterator::new(
                            arguments,
                            UnwrappedStreamDeserializer { s },
                            return_count,
                        )))
                    }
                    m if m == Bw6_761Field::id() => {
                        let s = p.into_iter::<Statement<Bw6_761Field>>();

                        Ok(ProgEnum::Bw6_761Program(ProgIterator::new(
                            arguments,
                            UnwrappedStreamDeserializer { s },
                            return_count,
                        )))
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
        p.clone().serialize(&mut buffer).unwrap();

        // rewind back to the beginning of the file
        buffer.seek(SeekFrom::Start(0)).unwrap();

        // deserialize
        let deserialized_p = ProgEnum::deserialize(buffer).unwrap();

        assert_eq!(ProgEnum::Bn128Program(p), deserialized_p.collect().unwrap());

        let p: ir::Prog<Bls12_381Field> = ir::Prog::default();

        let mut buffer = Cursor::new(vec![]);
        p.clone().serialize(&mut buffer).unwrap();

        // rewind back to the beginning of the file
        buffer.seek(SeekFrom::Start(0)).unwrap();

        // deserialize
        let deserialized_p = ProgEnum::deserialize(buffer).unwrap();

        assert_eq!(
            ProgEnum::Bls12_381Program(p),
            deserialized_p.collect().unwrap()
        );
    }
}
