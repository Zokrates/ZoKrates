use parser::parser_logic;
use program_structure::file_definition::FileLibrary;
use program_structure::program_archive::ProgramArchive;
use std::fmt;

pub fn parse(src: &str) -> CircomModule {
    let file_library = FileLibrary::new();
    let mut definitions = Vec::new();
    let mut main_components = Vec::new();

    let file_id = 0;

    let program = parser_logic::parse_file(&src, file_id)
        .map_err(|_| ())
        .unwrap();

    if let Some(main) = program.main_component {
        main_components.push((file_id, main));
    }
    let includes = program.includes;

    assert_eq!(includes.len(), 0);

    definitions.push((file_id, program.definitions));

    assert!(main_components.len() == 1);

    let (main_id, main_component) = main_components.pop().unwrap();
    let result_program_archive =
        ProgramArchive::new(file_library, main_id, main_component, definitions);

    CircomModule {
        program: result_program_archive.map_err(|_| ()).unwrap(),
        span: src,
    }
}

pub fn check(p: CircomModule) -> CircomModule {
    let mut p = p;

    type_analysis::check_types::check_types(&mut p.program)
        .map_err(|_| ())
        .unwrap();

    p
}

pub fn get_output_count(p: &CircomModule) -> usize {
    // match &p.program.initial_template_call {
    //     program_structure::abstract_syntax_tree::ast::Expression::Call {
    //         meta: _,
    //         id: _,
    //         args,
    //     } => dbg!(args.len()),
    //     _ => {
    //         unimplemented!();
    //     }
    // }
    1
}

pub fn get_input_count(p: &CircomModule) -> usize {
    p.program.public_inputs.len()
}

/// A circom module as a ProgramArchive
#[derive(Clone)]
pub struct CircomModule<'ast> {
    pub span: &'ast str,
    pub program: ProgramArchive,
}

impl<'ast> fmt::Debug for CircomModule<'ast> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.span)
    }
}

impl<'ast> fmt::Display for CircomModule<'ast> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.span)
    }
}

impl<'ast> PartialEq for CircomModule<'ast> {
    fn eq(&self, other: &Self) -> bool {
        self.span.eq(other.span)
    }
}

impl<'ast> Eq for CircomModule<'ast> {}

impl<'ast> PartialOrd for CircomModule<'ast> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        self.span.partial_cmp(other.span)
    }
}

impl<'ast> Ord for CircomModule<'ast> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.partial_cmp(other).unwrap()
    }
}

impl<'ast> std::hash::Hash for CircomModule<'ast> {
    fn hash<H: std::hash::Hasher>(&self, hasher: &mut H) {
        self.span.hash(hasher);
    }
}
