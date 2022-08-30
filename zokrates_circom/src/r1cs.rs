use byteorder::{LittleEndian, WriteBytesExt};
use std::collections::{BTreeSet, HashMap};
use std::io::Result;
use std::{io::Write, ops::Add};
use zokrates_ast::flat::Variable;
use zokrates_ast::ir::{Prog, Statement};
use zokrates_field::Field;
struct Header {
    pub field_size: u32,
    pub prime_size: Vec<u8>,
    pub n_wires: u32,
    pub n_pub_out: u32,
    pub n_pub_in: u32,
    pub n_prv_in: u32,
    pub n_labels: u64,
    pub n_constraints: u32,
}

type LinComb<T> = Vec<(usize, T)>;
type Constraint<T> = (LinComb<T>, LinComb<T>, LinComb<T>);

fn write_header<W: Write>(writer: &mut W, header: Header) -> Result<()> {
    writer.write_u32::<LittleEndian>(header.field_size)?;
    writer.write_all(&header.prime_size)?;
    writer.write_u32::<LittleEndian>(header.n_wires)?;
    writer.write_u32::<LittleEndian>(header.n_pub_out)?;
    writer.write_u32::<LittleEndian>(header.n_pub_in)?;
    writer.write_u32::<LittleEndian>(header.n_prv_in)?;
    writer.write_u64::<LittleEndian>(header.n_labels)?;
    writer.write_u32::<LittleEndian>(header.n_constraints)?;

    Ok(())
}

/// Returns the index of `var` in `variables`, adding `var` with incremented index if it does not yet exists.
///
/// # Arguments
///
/// * `variables` - A mutual map that maps all existing variables to their index.
/// * `var` - Variable to be searched for.
pub fn provide_variable_idx(variables: &mut HashMap<Variable, usize>, var: &Variable) -> usize {
    let index = variables.len();
    *variables.entry(*var).or_insert(index)
}

/// Calculates one R1CS row representation of a program and returns (V, A, B, C) so that:
/// * `V` contains all used variables and the index in the vector represents the used number in `A`, `B`, `C`
/// * `<A,x>*<B,x> = <C,x>` for a witness `x`
///
/// # Arguments
///
/// * `prog` - The program the representation is calculated for.
pub fn r1cs_program<T: Field>(prog: Prog<T>) -> (Vec<Variable>, usize, Vec<Constraint<T>>) {
    let mut variables: HashMap<Variable, usize> = HashMap::new();
    provide_variable_idx(&mut variables, &Variable::one());

    for i in 0..prog.return_count {
        provide_variable_idx(&mut variables, &Variable::public(i));
    }

    for x in prog.arguments.iter().filter(|p| !p.private) {
        provide_variable_idx(&mut variables, &x.id);
    }

    // position where private part of witness starts
    let private_inputs_offset = variables.len();

    // build a set of all variables
    let mut ordered_variables_set = BTreeSet::default();

    // first pass through statements to populate `variables`
    for (quad, lin) in prog.statements.iter().filter_map(|s| match s {
        Statement::Constraint(quad, lin, _) => Some((quad, lin)),
        Statement::Directive(..) => None,
        Statement::Log(..) => None,
    }) {
        for (k, _) in &quad.left.0 {
            ordered_variables_set.insert(k);
        }
        for (k, _) in &quad.right.0 {
            ordered_variables_set.insert(k);
        }
        for (k, _) in &lin.0 {
            ordered_variables_set.insert(k);
        }
    }

    // create indices for the variables *in increasing order*
    for variable in ordered_variables_set {
        provide_variable_idx(&mut variables, variable);
    }

    let mut constraints = vec![];

    // second pass to convert program to raw sparse vectors
    for (quad, lin) in prog.statements.into_iter().filter_map(|s| match s {
        Statement::Constraint(quad, lin, _) => Some((quad, lin)),
        Statement::Directive(..) => None,
        Statement::Log(..) => None,
    }) {
        constraints.push((
            quad.left
                .0
                .into_iter()
                .map(|(k, v)| (*variables.get(&k).unwrap(), v))
                .collect(),
            quad.right
                .0
                .into_iter()
                .map(|(k, v)| (*variables.get(&k).unwrap(), v))
                .collect(),
            lin.0
                .into_iter()
                .map(|(k, v)| (*variables.get(&k).unwrap(), v))
                .collect(),
        ));
    }

    // Convert map back into list ordered by index
    let mut variables_list = vec![Variable::new(0); variables.len()];
    for (k, v) in variables.drain() {
        assert_eq!(variables_list[v], Variable::new(0));
        variables_list[v] = k;
    }
    (variables_list, private_inputs_offset, constraints)
}

pub fn write_r1cs<T: Field, W: Write>(writer: &mut W, p: Prog<T>) -> Result<()> {
    let modulo_byte_count = T::max_value().to_biguint().add(1u32).to_bytes_le().len() as u32;

    let n_pub_out = p.return_count as u32;
    let n_pub_in = p.arguments.iter().filter(|a| !a.private).count() as u32;
    let n_prv_in = p.arguments.iter().filter(|a| a.private).count() as u32;

    let (vars, _, constraints) = r1cs_program(p);

    let n_wires = vars.len();

    let header = Header {
        field_size: modulo_byte_count,
        prime_size: T::max_value().to_biguint().add(1u32).to_bytes_le(),
        n_wires: n_wires as u32,
        n_pub_out,
        n_pub_in,
        n_prv_in,
        n_labels: n_wires as u64,
        n_constraints: constraints.len() as u32,
    };

    // magic
    writer.write_all(&[0x72, 0x31, 0x63, 0x73])?;
    // version
    writer.write_u32::<LittleEndian>(1)?;
    // section count
    writer.write_u32::<LittleEndian>(3)?;

    // section type: constraints
    // type
    writer.write_u32::<LittleEndian>(2)?;
    // size: 4 per lc + (32 + 4) per summand
    let size = constraints
        .iter()
        .map(|(a, b, c)| {
            (3 * 4 // for each lc, 4 bytes for its size
                    + (a.len() + b.len() + c.len()) // for each summand
                        * (modulo_byte_count as usize + 4)) // 4 bytes for the signal, `modulo_byte_count` bytes for the coefficient
                as u64
        })
        .sum();
    writer.write_u64::<LittleEndian>(size)?;

    write_constraints(writer, constraints)?;

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
    writer.write_u64::<LittleEndian>(n_wires as u64 * 8)?;

    write_table(writer, &vars)?;

    Ok(())
}

fn write_constraints<T: Field, W: Write>(
    writer: &mut W,
    constraints: Vec<Constraint<T>>,
) -> Result<()> {
    for c in constraints {
        write_lincomb(writer, c.0)?;
        write_lincomb(writer, c.1)?;
        write_lincomb(writer, c.2)?;
    }
    Ok(())
}

fn write_lincomb<T: Field, W: Write>(writer: &mut W, l: LinComb<T>) -> Result<()> {
    writer.write_u32::<LittleEndian>(l.len() as u32)?;
    for (var, coeff) in l {
        writer.write_u32::<LittleEndian>(var as u32)?;
        let mut res = vec![0u8; 32];
        for (value, padded) in coeff.to_biguint().to_bytes_le().iter().zip(res.iter_mut()) {
            *padded = *value;
        }
        writer.write_all(&res)?;
    }
    Ok(())
}

// for now we do not write any signal map
fn write_table<W: Write>(w: &mut W, variables: &[Variable]) -> Result<()> {
    for (i, _) in variables.iter().enumerate() {
        w.write_u64::<LittleEndian>(i as u64)?;
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use std::io::Cursor;

    use super::*;
    use pretty_assertions::assert_eq;
    use zkutil::r1cs_reader;
    use zokrates_ast::{
        flat::{Parameter, Variable},
        ir::{LinComb, QuadComb, Statement},
    };
    use zokrates_field::Bn128Field;

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
            // n wires
            0x01, 0x00, 0x00, 0x00,
            // n pub outputs
            0x00, 0x00, 0x00, 0x00,
            // n pub inputs
            0x00, 0x00, 0x00, 0x00,
            // n priv
            0x00, 0x00, 0x00, 0x00,
            // n labels
            0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            // n constraints 
            0x00, 0x00, 0x00, 0x00,
            // wire map (variable one?)
            0x03, 0x00, 0x00, 0x00, 0x08, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        ];

        write_r1cs(&mut buf, prog).unwrap();

        assert_eq!(buf, expected);

        let c = Cursor::new(buf);

        assert!(r1cs_reader::read(c).is_ok());
    }

    #[test]
    fn return_one() {
        let prog: Prog<Bn128Field> = Prog {
            arguments: vec![],
            return_count: 1,
            statements: vec![Statement::Constraint(
                LinComb::one().into(),
                Variable::public(0).into(),
                None,
            )],
        };

        let mut buf = Vec::new();

        #[rustfmt::skip]
        let expected: Vec<u8> = vec![
            0x72, 0x31, 0x63, 0x73,
            0x01, 0x00, 0x00, 0x00,
            0x03, 0x00, 0x00, 0x00,
            0x02, 0x00, 0x00, 0x00, 0x78, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, // size = 1 constraint = sum(4 /* write term_count_i */ + term_count_i * (4 + 32)) = 120
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
            // modulo size 
            0x20, 0x00, 0x00, 0x00, 
            // modulo
            0x01, 0x00, 0x00, 0xf0, 0x93, 0xf5, 0xe1, 0x43, 0x91, 0x70, 0xb9, 0x79, 0x48, 0xe8, 0x33, 0x28, 0x5d, 0x58, 0x81, 0x81, 0xb6, 0x45, 0x50, 0xb8, 0x29, 0xa0, 0x31, 0xe1, 0x72, 0x4e, 0x64, 0x30, 
            0x02, 0x00, 0x00, 0x00, 
            0x01, 0x00, 0x00, 0x00, 
            0x00, 0x00, 0x00, 0x00, 
            0x00, 0x00, 0x00, 0x00, 
            0x02, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 
            0x01, 0x00, 0x00, 0x00,
            // wire map (one, pub0)
            0x03, 0x00, 0x00, 0x00, 0x10, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 
            0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        ];

        write_r1cs(&mut buf, prog).unwrap();

        assert_eq!(buf, expected);

        let c = Cursor::new(buf);

        assert!(r1cs_reader::read(c).is_ok());
    }

    #[test]
    fn with_inputs() {
        let prog: Prog<Bn128Field> = Prog {
            arguments: vec![
                Parameter::private(Variable::new(0)),
                Parameter::public(Variable::new(1)),
            ],
            return_count: 1,
            statements: vec![
                Statement::Constraint(
                    QuadComb::from_linear_combinations(
                        LinComb::from(Variable::new(0)),
                        LinComb::from(Variable::new(0)),
                    ),
                    LinComb::from(Variable::new(0)),
                    None,
                ),
                Statement::Constraint(
                    (LinComb::from(Variable::new(0)) + LinComb::from(Variable::new(1))).into(),
                    Variable::public(0).into(),
                    None,
                ),
            ],
        };

        let mut buf = Vec::new();

        #[rustfmt::skip]
        let expected: Vec<u8> = vec![
            0x72, 0x31, 0x63, 0x73,
            0x01, 0x00, 0x00, 0x00,
            0x03, 0x00, 0x00, 0x00,
            0x02, 0x00, 0x00, 0x00, 0x14, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            // first constraint
            0x01, 0x00, 0x00, 0x00, // 1 element in this lc
            0x03, 0x00, 0x00, 0x00, // variable 3
            0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, // coeff 1
            0x01, 0x00, 0x00, 0x00, // 1 element in this lc
            0x03, 0x00, 0x00, 0x00, // variable 3
            0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, // coeff 1
            0x01, 0x00, 0x00, 0x00, // 1 element in this lc
            0x03, 0x00, 0x00, 0x00, // variable 3
            0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, // coeff 1
            // second constraint
            0x01, 0x00, 0x00, 0x00, // 1 element in this lc
            0x00, 0x00, 0x00, 0x00, // variable 0
            0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, // coeff 1
            0x02, 0x00, 0x00, 0x00, // 2 element in this lc
            0x03, 0x00, 0x00, 0x00, // variable 3
            0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, // coeff 1
            0x02, 0x00, 0x00, 0x00, // variable 2
            0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, // coeff 1
            0x01, 0x00, 0x00, 0x00, // 1 element in this lc
            0x01, 0x00, 0x00, 0x00, // variable 1
            0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, // coeff 1
            // header
            0x01, 0x00, 0x00, 0x00, 0x40, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            // modulo size 
            0x20, 0x00, 0x00, 0x00, 
            // modulo
            0x01, 0x00, 0x00, 0xf0, 0x93, 0xf5, 0xe1, 0x43, 0x91, 0x70, 0xb9, 0x79, 0x48, 0xe8, 0x33, 0x28, 0x5d, 0x58, 0x81, 0x81, 0xb6, 0x45, 0x50, 0xb8, 0x29, 0xa0, 0x31, 0xe1, 0x72, 0x4e, 0x64, 0x30, 
            0x04, 0x00, 0x00, 0x00, 
            0x01, 0x00, 0x00, 0x00, 
            0x01, 0x00, 0x00, 0x00, 
            0x01, 0x00, 0x00, 0x00, 
            0x04, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 
            0x02, 0x00, 0x00, 0x00,
            // wire map (one, ~out_0, _1, _0)
            0x03, 0x00, 0x00, 0x00, 0x20, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 
            0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x02, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x03, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        ];

        write_r1cs(&mut buf, prog).unwrap();

        assert_eq!(buf, expected);

        let c = Cursor::new(buf);

        assert!(r1cs_reader::read(c).is_ok());
    }
}
