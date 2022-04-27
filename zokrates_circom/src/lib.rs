use byteorder::{LittleEndian, WriteBytesExt};
use std::io::Result;
use std::{io::Write, ops::Add};
use zokrates_core::ir::{LinComb, Prog, Statement};
use zokrates_field::{Bn128Field, Field};

pub struct Header {
    pub field_size: u32,
    pub prime_size: Vec<u8>,
    pub n_wires: u32,
    pub n_pub_out: u32,
    pub n_pub_in: u32,
    pub n_prv_in: u32,
    pub n_labels: u64,
    pub n_constraints: u32,
}

fn write_header<W: Write>(writer: &mut W, header: Header) -> Result<()> {
    writer.write_u32::<LittleEndian>(header.field_size)?;
    writer.write(&header.prime_size)?;
    writer.write_u32::<LittleEndian>(header.n_wires)?;
    writer.write_u32::<LittleEndian>(header.n_pub_out)?;
    writer.write_u32::<LittleEndian>(header.n_pub_in)?;
    writer.write_u32::<LittleEndian>(header.n_prv_in)?;
    writer.write_u64::<LittleEndian>(header.n_labels)?;
    writer.write_u32::<LittleEndian>(header.n_constraints)?;

    Ok(())
}

pub fn write_r1cs<W: Write>(writer: &mut W, p: Prog<Bn128Field>) -> Result<()> {
    let header = Header {
        field_size: 32,
        prime_size: Bn128Field::max_value().to_biguint().add(1u32).to_bytes_le(),
        n_wires: 0, // TODO: count private variables
        n_pub_out: p.return_count as u32,
        n_pub_in: p.arguments.iter().filter(|a| !a.private).count() as u32,
        n_prv_in: p.arguments.iter().filter(|a| a.private).count() as u32,
        n_labels: 0,
        n_constraints: p.constraint_count() as u32,
    };

    let shift = header.n_pub_out + header.n_pub_in;

    // magic
    writer.write(&[0x72, 0x31, 0x63, 0x73])?;
    // version
    writer.write_u32::<LittleEndian>(1)?;
    // section count
    writer.write_u32::<LittleEndian>(3)?;

    // section type: constraints
    // type
    writer.write_u32::<LittleEndian>(2u32)?;
    // size: 4 per constraint + (32 + 4) per summand
    let size = p
        .statements
        .iter()
        .map(|s| match s {
            Statement::Constraint(q, l, _) => {
                ((q.left.0.len() + q.right.0.len() + l.0.len()) * (32 + 4) + 4) as u64
            }
            _ => 0,
        })
        .sum();
    writer.write_u64::<LittleEndian>(size)?;

    write_constraints(writer, &p, shift)?;

    // section type: header
    // type
    writer.write_u32::<LittleEndian>(1)?;
    // size
    writer.write_u64::<LittleEndian>(32 + 32)?;

    // header
    write_header(writer, header)?;

    // section type: wire2label
    // type
    writer.write_u32::<LittleEndian>(3)?;
    // size
    writer.write_u64::<LittleEndian>(0)?;

    write_table(writer, &p)?;

    Ok(())
}

fn write_constraints<W: Write>(writer: &mut W, p: &Prog<Bn128Field>, shift: u32) -> Result<()> {
    for s in &p.statements {
        write_statement(writer, s, shift)?;
    }
    Ok(())
}

fn write_statement<W: Write>(writer: &mut W, s: &Statement<Bn128Field>, shift: u32) -> Result<()> {
    match s {
        Statement::Constraint(quad, lin, _) => {
            let left = &quad.left;
            write_lincomb(writer, left, shift)?;
            let right = &quad.right;
            write_lincomb(writer, right, shift)?;
            write_lincomb(writer, lin, shift)?;
        }
        _ => {}
    };
    Ok(())
}

fn write_lincomb<W: Write>(writer: &mut W, l: &LinComb<Bn128Field>, shift: u32) -> Result<()> {
    writer.write_u32::<LittleEndian>(l.0.len() as u32)?;
    for (var, coeff) in &l.0 {
        let shift = shift as isize;
        let id = if var.id == 0 {
            0
        } else if var.id > 0 {
            var.id + shift
        } else {
            assert!(-var.id <= shift);
            -var.id
        } as u32;

        writer.write_u32::<LittleEndian>(id)?;
        let mut res = vec![0u8; 32];
        for (value, padded) in coeff.to_biguint().to_bytes_le().iter().zip(res.iter_mut()) {
            *padded = *value;
        }
        writer.write(&res)?;
    }
    Ok(())
}

// for now we do not write any signal map
fn write_table<W>(_: &mut W, _: &Prog<Bn128Field>) -> Result<()> {
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use pretty_assertions::assert_eq;
    use zokrates_core::{
        flat_absy::FlatVariable,
        ir::{LinComb, Statement},
    };

    #[test]
    fn empty() {
        let prog: Prog<Bn128Field> = Prog::default();
        let mut buf = Vec::new();

        #[rustfmt::skip]
        let expected: Vec<u8> = vec![
            // magic
            0x72, 0x31, 0x63, 0x73,
            // version
            0x01, 0x00, 0x00, 0x00,
            // section count
            0x03, 0x00, 0x00, 0x00, 
            // constraints section (empty)
            0x02, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 
            // header
            0x01, 0x00, 0x00, 0x00, 0x40, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 
            // modulus size in bytes
            0x20, 0x00, 0x00, 0x00, 
            // modulus
            0x01, 0x00, 0x00, 0xf0, 0x93, 0xf5, 0xe1, 0x43, 0x91, 0x70, 0xb9, 0x79, 0x48, 0xe8, 0x33, 0x28, 0x5d, 0x58, 0x81, 0x81, 0xb6, 0x45, 0x50, 0xb8, 0x29, 0xa0, 0x31, 0xe1, 0x72, 0x4e, 0x64, 0x30, 
            0x00, 0x00, 0x00, 0x00, 
            0x00, 0x00, 0x00, 0x00, 
            0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00, 
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 
            0x00, 0x00, 0x00, 0x00,
            // wire map (empty)
            0x03, 0x00, 0x00, 0x00, 
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        ];

        write_r1cs(&mut buf, prog).unwrap();

        assert_eq!(buf, expected);
    }

    #[test]
    fn return_one() {
        let prog: Prog<Bn128Field> = Prog {
            arguments: vec![],
            return_count: 1,
            statements: vec![Statement::Constraint(
                LinComb::one().into(),
                FlatVariable::public(0).into(),
                None,
            )],
        };
        let mut buf = Vec::new();

        #[rustfmt::skip]
        let expected: Vec<u8> = vec![
            0x72, 0x31, 0x63, 0x73,
            0x01, 0x00, 0x00, 0x00,
            0x03, 0x00, 0x00, 0x00,
            0x02, 0x00, 0x00, 0x00, 0x70, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, // size = 1 constraint = 3 * (4 /* term_count */ + term_count * (4 + 32)) = 112
            0x01, 0x00, 0x00, 0x00, // 1 element in this lc
            0x00, 0x00, 0x00, 0x00, // variable 0
            0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, // coeff 1
            0x01, 0x00, 0x00, 0x00, // 1 element in this lc
            0x00, 0x00, 0x00, 0x00, // variable 0
            0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, // coeff 1
            0x01, 0x00, 0x00, 0x00, // 1 element in this lc
            0x01, 0x00, 0x00, 0x00, // variable 1
            0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, // coeff 1
            // header
            0x01, 0x00, 0x00, 0x00, 0x40, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 
            0x20, 0x00, 0x00, 0x00, 
            0x01, 0x00, 0x00, 0xf0, 0x93, 0xf5, 0xe1, 0x43, 0x91, 0x70, 0xb9, 0x79, 0x48, 0xe8, 0x33, 0x28, 0x5d, 0x58, 0x81, 0x81, 0xb6, 0x45, 0x50, 0xb8, 0x29, 0xa0, 0x31, 0xe1, 0x72, 0x4e, 0x64, 0x30, 
            0x00, 0x00, 0x00, 0x00, 
            0x01, 0x00, 0x00, 0x00, 
            0x00, 0x00, 0x00, 0x00, 
            0x00, 0x00, 0x00, 0x00, 
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 
            0x01, 0x00, 0x00, 0x00,
            // wire map (empty)
            0x03, 0x00, 0x00, 0x00, 
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        ];

        write_r1cs(&mut buf, prog).unwrap();

        assert_eq!(buf, expected);
    }
}
