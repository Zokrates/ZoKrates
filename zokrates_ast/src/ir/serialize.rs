use crate::ir::check::UnconstrainedVariableDetector;

use super::{ProgIterator, Statement};
use serde_cbor::{self, StreamDeserializer};
use std::io::{Read, Write};
use zokrates_field::*;

type DynamicError = Box<dyn std::error::Error>;

const ZOKRATES_MAGIC: &[u8; 4] = &[0x5a, 0x4f, 0x4b, 0];
const ZOKRATES_VERSION_2: &[u8; 4] = &[0, 0, 0, 2];

#[derive(PartialEq, Eq, Debug)]
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
    pub fn curve(&self) -> &'static str {
        match self {
            ProgEnum::Bn128Program(_) => Bn128Field::name(),
            ProgEnum::Bls12_381Program(_) => Bls12_381Field::name(),
            ProgEnum::Bls12_377Program(_) => Bls12_377Field::name(),
            ProgEnum::Bw6_761Program(_) => Bw6_761Field::name(),
        }
    }
}

impl<T: Field, I: IntoIterator<Item = Statement<T>>> ProgIterator<T, I> {
    /// serialize a program iterator, returning the number of constraints serialized
    /// Note that we only return constraints, not other statements such as directives
    pub fn serialize<W: Write>(self, mut w: W) -> Result<usize, DynamicError> {
        use super::folder::Folder;

        w.write_all(ZOKRATES_MAGIC)?;
        w.write_all(ZOKRATES_VERSION_2)?;
        w.write_all(&T::id())?;

        serde_cbor::to_writer(&mut w, &self.arguments)?;
        serde_cbor::to_writer(&mut w, &self.return_count)?;

        let mut unconstrained_variable_detector = UnconstrainedVariableDetector::new(&self);

        let statements = self.statements.into_iter();

        let mut count = 0;
        for s in statements {
            if matches!(s, Statement::Constraint(..)) {
                count += 1;
            }
            let s = unconstrained_variable_detector.fold_statement(s);
            for s in s {
                serde_cbor::to_writer(&mut w, &s)?;
            }
        }

        unconstrained_variable_detector
            .finalize()
            .map(|_| count)
            .map_err(|count| format!("Error: Found {} unconstrained variable(s)", count).into())
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
                    type Value = Vec<super::Parameter>;
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
    use crate::ir::Prog;
    use std::io::{Cursor, Seek, SeekFrom};
    use zokrates_field::{Bls12_381Field, Bn128Field};

    #[test]
    fn ser_deser_v2() {
        let p: Prog<Bn128Field> = Prog::default();

        let mut buffer = Cursor::new(vec![]);
        p.clone().serialize(&mut buffer).unwrap();

        // rewind back to the beginning of the file
        buffer.seek(SeekFrom::Start(0)).unwrap();

        // deserialize
        let deserialized_p = ProgEnum::deserialize(buffer).unwrap();

        assert_eq!(ProgEnum::Bn128Program(p), deserialized_p.collect());

        let p: Prog<Bls12_381Field> = Prog::default();

        let mut buffer = Cursor::new(vec![]);
        p.clone().serialize(&mut buffer).unwrap();

        // rewind back to the beginning of the file
        buffer.seek(SeekFrom::Start(0)).unwrap();

        // deserialize
        let deserialized_p = ProgEnum::deserialize(buffer).unwrap();

        assert_eq!(ProgEnum::Bls12_381Program(p), deserialized_p.collect());
    }
}
