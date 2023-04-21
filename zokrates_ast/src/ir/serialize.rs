use crate::ir::{check::UnconstrainedVariableDetector, solver_indexer::SolverIndexer};

use super::{ProgIterator, Statement};
use crate::ir::ModuleMap;
use byteorder::{LittleEndian, ReadBytesExt, WriteBytesExt};
use serde::Deserialize;
use serde_cbor::{self, StreamDeserializer};
use std::io::{Read, Seek, Write};
use zokrates_field::*;

type DynamicError = Box<dyn std::error::Error>;

const ZOKRATES_MAGIC: &[u8; 4] = &[0x5a, 0x4f, 0x4b, 0];
const FILE_VERSION: &[u8; 4] = &[3, 0, 0, 0];

#[derive(PartialEq, Eq, Debug)]
pub enum ProgEnum<
    'ast,
    Bls12_381I: IntoIterator<Item = Statement<'ast, Bls12_381Field>>,
    Bn128I: IntoIterator<Item = Statement<'ast, Bn128Field>>,
    Bls12_377I: IntoIterator<Item = Statement<'ast, Bls12_377Field>>,
    Bw6_761I: IntoIterator<Item = Statement<'ast, Bw6_761Field>>,
    PallasI: IntoIterator<Item = Statement<'ast, PallasField>>,
    VestaI: IntoIterator<Item = Statement<'ast, VestaField>>,
> {
    Bls12_381Program(ProgIterator<'ast, Bls12_381Field, Bls12_381I>),
    Bn128Program(ProgIterator<'ast, Bn128Field, Bn128I>),
    Bls12_377Program(ProgIterator<'ast, Bls12_377Field, Bls12_377I>),
    Bw6_761Program(ProgIterator<'ast, Bw6_761Field, Bw6_761I>),
    PallasProgram(ProgIterator<'ast, PallasField, PallasI>),
    VestaProgram(ProgIterator<'ast, VestaField, VestaI>),
}

type MemoryProgEnum<'ast> = ProgEnum<
    'ast,
    Vec<Statement<'ast, Bls12_381Field>>,
    Vec<Statement<'ast, Bn128Field>>,
    Vec<Statement<'ast, Bls12_377Field>>,
    Vec<Statement<'ast, Bw6_761Field>>,
    Vec<Statement<'ast, PallasField>>,
    Vec<Statement<'ast, VestaField>>,
>;

impl<
        'ast,
        Bls12_381I: IntoIterator<Item = Statement<'ast, Bls12_381Field>>,
        Bn128I: IntoIterator<Item = Statement<'ast, Bn128Field>>,
        Bls12_377I: IntoIterator<Item = Statement<'ast, Bls12_377Field>>,
        Bw6_761I: IntoIterator<Item = Statement<'ast, Bw6_761Field>>,
        PallasI: IntoIterator<Item = Statement<'ast, PallasField>>,
        VestaI: IntoIterator<Item = Statement<'ast, VestaField>>,
    > ProgEnum<'ast, Bls12_381I, Bn128I, Bls12_377I, Bw6_761I, PallasI, VestaI>
{
    pub fn collect(self) -> MemoryProgEnum<'ast> {
        match self {
            ProgEnum::Bls12_381Program(p) => ProgEnum::Bls12_381Program(p.collect()),
            ProgEnum::Bn128Program(p) => ProgEnum::Bn128Program(p.collect()),
            ProgEnum::Bls12_377Program(p) => ProgEnum::Bls12_377Program(p.collect()),
            ProgEnum::Bw6_761Program(p) => ProgEnum::Bw6_761Program(p.collect()),
            ProgEnum::PallasProgram(p) => ProgEnum::PallasProgram(p.collect()),
            ProgEnum::VestaProgram(p) => ProgEnum::VestaProgram(p.collect()),
        }
    }
    pub fn curve(&self) -> &'static str {
        match self {
            ProgEnum::Bn128Program(_) => Bn128Field::name(),
            ProgEnum::Bls12_381Program(_) => Bls12_381Field::name(),
            ProgEnum::Bls12_377Program(_) => Bls12_377Field::name(),
            ProgEnum::Bw6_761Program(_) => Bw6_761Field::name(),
            ProgEnum::PallasProgram(_) => Bls12_377Field::name(),
            ProgEnum::VestaProgram(_) => Bw6_761Field::name(),
        }
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
#[repr(u32)]
pub enum SectionType {
    Parameters = 1,
    Constraints = 2,
    Solvers = 3,
    Modules = 4,
}

impl TryFrom<u32> for SectionType {
    type Error = String;

    fn try_from(value: u32) -> Result<Self, Self::Error> {
        match value {
            1 => Ok(SectionType::Parameters),
            2 => Ok(SectionType::Constraints),
            3 => Ok(SectionType::Solvers),
            4 => Ok(SectionType::Modules),
            _ => Err("invalid section type".to_string()),
        }
    }
}

#[derive(Debug, Clone)]
pub struct Section {
    pub ty: SectionType,
    pub offset: u64,
    pub length: u64,
}

impl Section {
    pub fn new(ty: SectionType) -> Self {
        Self {
            ty,
            offset: 0,
            length: 0,
        }
    }

    pub fn set_offset(&mut self, offset: u64) {
        self.offset = offset;
    }

    pub fn set_length(&mut self, length: u64) {
        self.length = length;
    }
}

#[derive(Debug, Clone)]
pub struct ProgHeader {
    pub magic: [u8; 4],
    pub version: [u8; 4],
    pub curve_id: [u8; 4],
    pub constraint_count: u32,
    pub return_count: u32,
    pub sections: [Section; 4],
}

impl ProgHeader {
    pub fn write<W: Write>(&self, mut w: W) -> std::io::Result<()> {
        w.write_all(&self.magic)?;
        w.write_all(&self.version)?;
        w.write_all(&self.curve_id)?;
        w.write_u32::<LittleEndian>(self.constraint_count)?;
        w.write_u32::<LittleEndian>(self.return_count)?;

        for s in &self.sections {
            w.write_u32::<LittleEndian>(s.ty as u32)?;
            w.write_u64::<LittleEndian>(s.offset)?;
            w.write_u64::<LittleEndian>(s.length)?;
        }

        Ok(())
    }

    pub fn read<R: Read>(mut r: R) -> std::io::Result<Self> {
        let mut magic = [0; 4];
        r.read_exact(&mut magic)?;

        let mut version = [0; 4];
        r.read_exact(&mut version)?;

        let mut curve_id = [0; 4];
        r.read_exact(&mut curve_id)?;

        let constraint_count = r.read_u32::<LittleEndian>()?;
        let return_count = r.read_u32::<LittleEndian>()?;

        let parameters = Self::read_section(r.by_ref())?;
        let constraints = Self::read_section(r.by_ref())?;
        let solvers = Self::read_section(r.by_ref())?;
        let module_map = Self::read_section(r.by_ref())?;

        Ok(ProgHeader {
            magic,
            version,
            curve_id,
            constraint_count,
            return_count,
            sections: [parameters, constraints, solvers, module_map],
        })
    }

    fn read_section<R: Read>(mut r: R) -> std::io::Result<Section> {
        let id = r.read_u32::<LittleEndian>()?;
        let mut section = Section::new(
            SectionType::try_from(id)
                .map_err(|e| std::io::Error::new(std::io::ErrorKind::InvalidData, e))?,
        );
        section.set_offset(r.read_u64::<LittleEndian>()?);
        section.set_length(r.read_u64::<LittleEndian>()?);
        Ok(section)
    }
}

impl<'ast, T: Field, I: IntoIterator<Item = Statement<'ast, T>>> ProgIterator<'ast, T, I> {
    /// serialize a program iterator, returning the number of constraints serialized
    /// Note that we only return constraints, not other statements such as directives
    pub fn serialize<W: Write + Seek>(self, mut w: W) -> Result<usize, DynamicError> {
        use super::folder::Folder;

        // reserve bytes for the header
        w.write_all(&[0u8; std::mem::size_of::<ProgHeader>()])?;

        // write parameters section
        let parameters = {
            let mut section = Section::new(SectionType::Parameters);
            section.set_offset(w.stream_position()?);

            serde_cbor::to_writer(&mut w, &self.arguments)?;

            section.set_length(w.stream_position()? - section.offset);
            section
        };

        let mut solver_indexer: SolverIndexer<'ast, T> = SolverIndexer::default();
        let mut unconstrained_variable_detector = UnconstrainedVariableDetector::new(&self);
        let mut count: usize = 0;

        // write constraints section
        let constraints = {
            let mut section = Section::new(SectionType::Constraints);
            section.set_offset(w.stream_position()?);

            let statements = self.statements.into_iter();
            for s in statements {
                if matches!(s, Statement::Constraint(..)) {
                    count += 1;
                }
                let s: Vec<Statement<T>> = solver_indexer
                    .fold_statement(s)
                    .into_iter()
                    .flat_map(|s| unconstrained_variable_detector.fold_statement(s))
                    .collect();
                for s in s {
                    serde_cbor::to_writer(&mut w, &s)?;
                }
            }

            section.set_length(w.stream_position()? - section.offset);
            section
        };

        // write solvers section
        let solvers = {
            let mut section = Section::new(SectionType::Solvers);
            section.set_offset(w.stream_position()?);

            serde_cbor::to_writer(&mut w, &solver_indexer.solvers)?;

            section.set_length(w.stream_position()? - section.offset);
            section
        };

        // write module map section
        let module_map = {
            let mut section = Section::new(SectionType::Solvers);
            section.set_offset(w.stream_position()?);

            serde_cbor::to_writer(&mut w, &self.module_map)?;

            section.set_length(w.stream_position()? - section.offset);
            section
        };

        let header = ProgHeader {
            magic: *ZOKRATES_MAGIC,
            version: *FILE_VERSION,
            curve_id: T::id(),
            constraint_count: count as u32,
            return_count: self.return_count as u32,
            sections: [parameters, constraints, solvers, module_map],
        };

        // rewind to write the header
        w.rewind()?;
        header.write(&mut w)?;

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
        self.s.next().and_then(|v| v.ok())
    }
}

impl<'de, R: Read + Seek>
    ProgEnum<
        'de,
        UnwrappedStreamDeserializer<'de, serde_cbor::de::IoRead<R>, Statement<'de, Bls12_381Field>>,
        UnwrappedStreamDeserializer<'de, serde_cbor::de::IoRead<R>, Statement<'de, Bn128Field>>,
        UnwrappedStreamDeserializer<'de, serde_cbor::de::IoRead<R>, Statement<'de, Bls12_377Field>>,
        UnwrappedStreamDeserializer<'de, serde_cbor::de::IoRead<R>, Statement<'de, Bw6_761Field>>,
        UnwrappedStreamDeserializer<'de, serde_cbor::de::IoRead<R>, Statement<'de, PallasField>>,
        UnwrappedStreamDeserializer<'de, serde_cbor::de::IoRead<R>, Statement<'de, VestaField>>,
    >
{
    fn read<T: Field>(
        mut r: R,
        header: &ProgHeader,
    ) -> ProgIterator<
        'de,
        T,
        UnwrappedStreamDeserializer<'de, serde_cbor::de::IoRead<R>, Statement<'de, T>>,
    > {
        let parameters = {
            let section = &header.sections[0];
            r.seek(std::io::SeekFrom::Start(section.offset)).unwrap();

            let mut p = serde_cbor::Deserializer::from_reader(r.by_ref());
            Vec::deserialize(&mut p)
                .map_err(|_| String::from("Cannot read parameters"))
                .unwrap()
        };

        let solvers = {
            let section = &header.sections[2];
            r.seek(std::io::SeekFrom::Start(section.offset)).unwrap();

            let mut p = serde_cbor::Deserializer::from_reader(r.by_ref());
            Vec::deserialize(&mut p)
                .map_err(|_| String::from("Cannot read solvers"))
                .unwrap()
        };

        let module_map = {
            let section = &header.sections[3];
            r.seek(std::io::SeekFrom::Start(section.offset)).unwrap();

            let mut p = serde_cbor::Deserializer::from_reader(r.by_ref());
            ModuleMap::deserialize(&mut p)
                .map_err(|_| String::from("Cannot read module map"))
                .unwrap()
        };

        let statements_deserializer = {
            let section = &header.sections[1];
            r.seek(std::io::SeekFrom::Start(section.offset)).unwrap();

            let p = serde_cbor::Deserializer::from_reader(r);
            let s = p.into_iter::<Statement<T>>();

            UnwrappedStreamDeserializer { s }
        };

        ProgIterator::new(
            parameters,
            statements_deserializer,
            header.return_count as usize,
            module_map,
            solvers,
        )
    }

    pub fn deserialize(mut r: R) -> Result<Self, String> {
        let header = ProgHeader::read(&mut r).map_err(|_| String::from("Invalid header"))?;

        // Check the magic number, `ZOK`
        if &header.magic != ZOKRATES_MAGIC {
            return Err("Invalid magic number".to_string());
        }

        // Check the file version
        if &header.version != FILE_VERSION {
            return Err("Invalid file version".to_string());
        }

        match header.curve_id {
            m if m == Bls12_381Field::id() => {
                Ok(ProgEnum::Bls12_381Program(Self::read(r, &header)))
            }
            m if m == Bn128Field::id() => Ok(ProgEnum::Bn128Program(Self::read(r, &header))),
            m if m == Bls12_377Field::id() => {
                Ok(ProgEnum::Bls12_377Program(Self::read(r, &header)))
            }
            m if m == Bw6_761Field::id() => Ok(ProgEnum::Bw6_761Program(Self::read(r, &header))),
            m if m == PallasField::id() => Ok(ProgEnum::PallasProgram(Self::read(r, &header))),
            m if m == VestaField::id() => Ok(ProgEnum::VestaProgram(Self::read(r, &header))),
            _ => Err(String::from("Unknown curve identifier")),
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
