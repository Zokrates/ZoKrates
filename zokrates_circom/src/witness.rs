use std::{
    io::{Result, Write},
    ops::Add,
};

use byteorder::{LittleEndian, WriteBytesExt};
use zokrates_ast::{
    flat::Variable,
    ir::{PublicInputs, Witness},
};
use zokrates_field::Field;

pub struct Header {
    pub field_size: u32,
    pub prime_size: Vec<u8>,
    pub witness_size: u32,
}

fn write_header<W: Write>(writer: &mut W, header: Header) -> Result<()> {
    writer.write_u32::<LittleEndian>(header.field_size)?;
    writer.write_all(&header.prime_size)?;
    writer.write_u32::<LittleEndian>(header.witness_size)?;

    Ok(())
}

pub fn write_witness<T: Field, W: Write>(
    writer: &mut W,
    w: Witness<T>,
    public_inputs: PublicInputs,
) -> Result<()> {
    let modulo_byte_count = T::max_value().to_biguint().add(1u32).to_bytes_le().len() as u32;
    let witness_size = w.0.len() as u32;

    let header = Header {
        field_size: modulo_byte_count,
        prime_size: T::max_value().to_biguint().add(1u32).to_bytes_le(),
        witness_size,
    };

    // magic "wtns"
    writer.write_all(&[0x77, 0x74, 0x6e, 0x73])?;
    // version
    writer.write_u32::<LittleEndian>(2)?;
    // section count
    writer.write_u32::<LittleEndian>(2)?;

    // section type: header
    // type
    writer.write_u32::<LittleEndian>(1)?;
    // size
    writer.write_u64::<LittleEndian>(8 + modulo_byte_count as u64)?;

    // header
    write_header(writer, header)?;

    // section type: witness
    // type
    writer.write_u32::<LittleEndian>(2)?;
    // size: `modulo_byte_count` per witness value
    let size = witness_size as u64 * modulo_byte_count as u64;
    writer.write_u64::<LittleEndian>(size)?;

    write_witness_values(writer, w, public_inputs)?;

    Ok(())
}

fn write_val<T: Field, W: Write>(writer: &mut W, v: &T, modulo_byte_count: usize) -> Result<()> {
    let mut res = vec![0u8; modulo_byte_count];
    for (value, padded) in v.to_biguint().to_bytes_le().iter().zip(res.iter_mut()) {
        *padded = *value;
    }
    writer.write_all(&res)?;
    Ok(())
}

fn write_witness_values<T: Field, W: Write>(
    writer: &mut W,
    mut w: Witness<T>,
    public_inputs: PublicInputs,
) -> Result<()> {
    let modulo_byte_count = T::max_value().to_biguint().add(1u32).to_bytes_le().len();

    if let Some(value) = w.0.remove(&Variable::one()) {
        write_val(writer, &value, modulo_byte_count)?;
    }

    let output_count = w.0.iter().filter(|(var, _)| var.is_output()).count();

    for value in (0..output_count).map(|id| w.0.remove(&Variable::public(id)).unwrap()) {
        write_val(writer, &value, modulo_byte_count)?;
    }

    for value in public_inputs.iter().map(|var| w.0.remove(var).unwrap()) {
        write_val(writer, &value, modulo_byte_count)?;
    }

    for (_, val) in w.0.iter() {
        write_val(writer, val, modulo_byte_count)?;
    }

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use pretty_assertions::assert_eq;
    use zokrates_ast::{flat::Variable, ir::PublicInputs};
    use zokrates_field::Bn128Field;

    #[test]
    fn empty() {
        let w: Witness<Bn128Field> = Witness::default();
        let public_inputs: PublicInputs = Default::default();
        let mut buf = Vec::new();

        #[rustfmt::skip]
        let expected: Vec<u8> = vec![
            // magic
            0x77, 0x74, 0x6e, 0x73,
            // version
            0x02, 0x00, 0x00, 0x00,
            // section count
            0x02, 0x00, 0x00, 0x00, 
            // header
            0x01, 0x00, 0x00, 0x00, 0x28, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 
            // modulus size in bytes
            0x20, 0x00, 0x00, 0x00, 
            // modulus
            0x01, 0x00, 0x00, 0xf0, 0x93, 0xf5, 0xe1, 0x43, 0x91, 0x70, 0xb9, 0x79, 0x48, 0xe8, 0x33, 0x28, 0x5d, 0x58, 0x81, 0x81, 0xb6, 0x45, 0x50, 0xb8, 0x29, 0xa0, 0x31, 0xe1, 0x72, 0x4e, 0x64, 0x30, 
            // witness size
            0x00, 0x00, 0x00, 0x00,
            // witness section (empty)
            0x02, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 
        ];

        write_witness(&mut buf, w, public_inputs).unwrap();

        assert_eq!(buf, expected);
    }

    #[test]
    fn one_value() {
        let mut w: Witness<Bn128Field> = Witness::default();
        let public_inputs: PublicInputs = Default::default();
        w.0.insert(Variable::public(0), 1.into());
        let mut buf = Vec::new();

        #[rustfmt::skip]
        let expected: Vec<u8> = vec![
            // magic
            0x77, 0x74, 0x6e, 0x73,
            // version
            0x02, 0x00, 0x00, 0x00,
            // section count
            0x02, 0x00, 0x00, 0x00, 
            // header
            0x01, 0x00, 0x00, 0x00, 0x28, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 
            // modulus size in bytes
            0x20, 0x00, 0x00, 0x00, 
            // modulus
            0x01, 0x00, 0x00, 0xf0, 0x93, 0xf5, 0xe1, 0x43, 0x91, 0x70, 0xb9, 0x79, 0x48, 0xe8, 0x33, 0x28, 0x5d, 0x58, 0x81, 0x81, 0xb6, 0x45, 0x50, 0xb8, 0x29, 0xa0, 0x31, 0xe1, 0x72, 0x4e, 0x64, 0x30, 
            // witness size
            0x01, 0x00, 0x00, 0x00,
            // witness section
            0x02, 0x00, 0x00, 0x00, 0x20, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            // values
            0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        ];

        write_witness(&mut buf, w, public_inputs).unwrap();

        assert_eq!(buf, expected);
    }

    #[test]
    fn one_and_pub_and_priv() {
        let mut w: Witness<Bn128Field> = Witness::default();
        let public_inputs: PublicInputs = vec![Variable::new(1)].into_iter().collect();
        w.0.extend(vec![
            (Variable::public(0), 42.into()),
            (Variable::one(), 1.into()),
            (Variable::new(0), 43.into()),
            (Variable::new(1), 44.into()),
        ]);
        let mut buf = Vec::new();

        #[rustfmt::skip]
        let expected: Vec<u8> = vec![
            // magic
            0x77, 0x74, 0x6e, 0x73,
            // version
            0x02, 0x00, 0x00, 0x00,
            // section count
            0x02, 0x00, 0x00, 0x00, 
            // header
            0x01, 0x00, 0x00, 0x00, 0x28, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 
            // modulus size in bytes
            0x20, 0x00, 0x00, 0x00, 
            // modulus
            0x01, 0x00, 0x00, 0xf0, 0x93, 0xf5, 0xe1, 0x43, 0x91, 0x70, 0xb9, 0x79, 0x48, 0xe8, 0x33, 0x28, 0x5d, 0x58, 0x81, 0x81, 0xb6, 0x45, 0x50, 0xb8, 0x29, 0xa0, 0x31, 0xe1, 0x72, 0x4e, 0x64, 0x30, 
            // witness size
            0x04, 0x00, 0x00, 0x00,
            // witness section
            0x02, 0x00, 0x00, 0x00, 0x80, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            // values: ordering should be [one, ~out_0, _1, _0] because _1 is public
            0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x2a, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x2c, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x2b, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        ];

        write_witness(&mut buf, w, public_inputs).unwrap();

        assert_eq!(buf, expected);
    }
}
