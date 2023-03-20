#![allow(clippy::upper_case_acronyms)] // we allow uppercase acronyms because the pest derive generates WHITESPACE and COMMENT which have special meaning in pest

extern crate pest;
#[macro_use]
extern crate pest_derive;

use pest::error::Error;
use pest::iterators::Pairs;
use pest::Parser;

#[derive(Parser)]
#[grammar = "zokrates.pest"]
struct ZoKratesParser;

#[allow(clippy::result_large_err)]
pub fn parse(input: &str) -> Result<Pairs<Rule>, Error<Rule>> {
    ZoKratesParser::parse(Rule::file, input)
}

#[cfg(test)]
mod tests {
    use super::*;
    use pest::*;

    mod examples {
        use super::*;

        #[test]
        fn examples_dir() {
            use glob::glob;
            use std::fs;
            use std::io::Read;
            // Traverse all .zok files in examples dir
            for entry in
                glob("../zokrates_cli/examples/**/*.zok").expect("Failed to read glob pattern")
            {
                match entry {
                    Ok(path) => {
                        if path.to_str().unwrap().contains("error") {
                            continue;
                        }

                        println!("Parsing {:?}", path.display());
                        let mut file = fs::File::open(path).unwrap();

                        let mut data = String::new();
                        file.read_to_string(&mut data).unwrap();

                        assert!(ZoKratesParser::parse(Rule::file, &data).is_ok());
                    }
                    Err(e) => panic!("{:?}", e),
                }
            }
        }
    }

    mod rules {
        use super::*;

        // TODO: uncomment these tests once https://github.com/pest-parser/pest/pull/493 is resolved

        // #[test]
        // fn parse_valid_identifier() {
        //     parses_to! {
        //         parser: ZoKratesParser,
        //         input: "valididentifier_01",
        //         rule: Rule::identifier,
        //         tokens: [
        //             identifier(0, 18)
        //         ]
        //     };
        // }

        // #[test]
        // fn parse_parameter_list() {
        //     parses_to! {
        //         parser: ZoKratesParser,
        //         input: "def foo<P, Q>(field[P] a) -> (field, field): return 1
        //         ",
        //         rule: Rule::function_definition,
        //         tokens: [
        //             function_definition(0, 54, [
        //                 identifier(4, 7),
        //                 identifier(8, 9),
        //                 identifier(11, 12),
        //                 // parameter_list is not created (silent rule)
        //                 parameter(14, 24, [
        //                     ty(14, 23, [
        //                         ty_array(14, 23, [
        //                             ty_basic_or_struct(14, 19, [
        //                                 ty_basic(14, 19, [
        //                                     ty_field(14, 19)
        //                                 ])
        //                             ]),
        //                             expression(20, 21, [
        //                                 term(20, 21, [
        //                                     primary_expression(20, 21, [
        //                                         identifier(20, 21)
        //                                     ])
        //                                 ])
        //                             ])
        //                         ])
        //                     ]),
        //                     identifier(23, 24)
        //                 ]),
        //                 // type_list is not created (silent rule)
        //                 ty(30, 35, [
        //                     ty_basic(30, 35, [
        //                         ty_field(30, 35)
        //                     ])
        //                 ]),
        //                 ty(37, 42, [
        //                     ty_basic(37, 42, [
        //                         ty_field(37, 42)
        //                     ])
        //                 ]),
        //                 statement(45, 54, [
        //                     return_statement(45, 53, [
        //                         expression(52, 53, [
        //                             term(52, 53, [
        //                                 primary_expression(52, 53, [
        //                                     literal(52, 53, [
        //                                         decimal_literal(52, 53, [
        //                                             decimal_number(52, 53)
        //                                         ])
        //                                     ])
        //                                 ])
        //                             ])
        //                         ])
        //                     ])
        //                 ])
        //             ])
        //         ]
        //     };
        // }

        // #[test]
        // fn parse_single_def_to_multi() {
        //     parses_to! {
        //         parser: ZoKratesParser,
        //         input: r#"a = foo::<_>(x)
        //     "#,
        //         rule: Rule::statement,
        //         tokens: [
        //             statement(0, 28, [
        //                 definition_statement(0, 15, [
        //                     optionally_typed_assignee(0, 2, [
        //                         assignee(0, 2, [
        //                             identifier(0, 1)
        //                         ])
        //                     ]),
        //                     expression(4, 15, [
        //                         term(4, 15, [
        //                             postfix_expression(4, 15, [
        //                                 identifier(4, 7),
        //                                 access(7, 15, [
        //                                     call_access(7, 15, [
        //                                         explicit_generics(7, 12, [
        //                                             constant_generics_value(10, 11, [
        //                                                 underscore(10, 11)
        //                                             ])
        //                                         ]),
        //                                         arguments(13, 14, [
        //                                             expression(13, 14, [
        //                                                 term(13, 14, [
        //                                                     primary_expression(13, 14, [
        //                                                         identifier(13, 14)
        //                                                     ])
        //                                                 ])
        //                                             ])
        //                                         ])
        //                                     ])
        //                                 ])
        //                             ])
        //                         ])
        //                     ]),
        //                 ])
        //             ])
        //         ]
        //     };
        // }

        // #[test]
        // fn parse_field_def_to_multi() {
        //     parses_to! {
        //         parser: ZoKratesParser,
        //         input: r#"field a = foo()
        //     "#,
        //         rule: Rule::statement,
        //         tokens: [
        //             statement(0, 28, [
        //                 definition_statement(0, 15, [
        //                     optionally_typed_assignee(0, 8, [
        //                         ty(0, 5, [
        //                             ty_basic(0, 5, [
        //                                 ty_field(0, 5)
        //                             ])
        //                         ]),
        //                         assignee(6, 8, [
        //                             identifier(6, 7)
        //                         ])
        //                     ]),
        //                     expression(10, 15, [
        //                         term(10, 15, [
        //                             postfix_expression(10, 15, [
        //                                 identifier(10, 13),
        //                                 access(13, 15, [
        //                                     call_access(13, 15, [
        //                                         arguments(14, 14)
        //                                     ])
        //                                 ])
        //                             ])
        //                         ])
        //                     ]),
        //                 ])
        //             ])
        //         ]
        //     };
        // }

        // #[test]
        // fn parse_u8_def_to_multi() {
        //     parses_to! {
        //         parser: ZoKratesParser,
        //         input: r#"u32 a = foo()
        //     "#,
        //         rule: Rule::statement,
        //         tokens: [
        //             statement(0, 26, [
        //                 definition_statement(0, 13, [
        //                     optionally_typed_assignee(0, 6, [
        //                         ty(0, 3, [
        //                             ty_basic(0, 3, [
        //                                 ty_u32(0, 3)
        //                             ])
        //                         ]),
        //                         assignee(4, 6, [
        //                             identifier(4, 5)
        //                         ])
        //                     ]),
        //                     expression(8, 13, [
        //                         term(8, 13, [
        //                             postfix_expression(8, 13, [
        //                                 identifier(8, 11),
        //                                 access(11, 13, [
        //                                     call_access(11, 13, [
        //                                         arguments(12, 12)
        //                                     ])
        //                                 ])
        //                             ])
        //                         ])
        //                     ]),
        //                 ])
        //             ])
        //         ]
        //     };
        // }

        // #[test]
        // fn parse_invalid_identifier() {
        //     fails_with! {
        //         parser: ZoKratesParser,
        //         input: "0_invalididentifier",
        //         rule: Rule::identifier,
        //         positives: vec![Rule::identifier],
        //         negatives: vec![],
        //         pos: 0
        //     };
        // }

        // #[test]
        // fn parse_struct_def() {
        //     parses_to! {
        //         parser: ZoKratesParser,
        //         input: "struct Foo { field foo\n field[2] bar }
        //         ",
        //         rule: Rule::ty_struct_definition,
        //         tokens: [
        //             ty_struct_definition(0, 39, [
        //                 identifier(7, 10),
        //                 struct_field(13, 22, [
        //                     ty(13, 18, [
        //                         ty_basic(13, 18, [
        //                             ty_field(13, 18)
        //                         ])
        //                     ]),
        //                     identifier(19, 22)
        //                 ]),
        //                 struct_field(24, 36, [
        //                     ty(24, 33, [
        //                         ty_array(24, 33, [
        //                             ty_basic_or_struct(24, 29, [
        //                                 ty_basic(24, 29, [
        //                                     ty_field(24, 29)
        //                                 ])
        //                             ]),
        //                             expression(30, 31, [
        //                                 term(30, 31, [
        //                                     primary_expression(30, 31, [
        //                                         literal(30, 31, [
        //                                             decimal_literal(30, 31, [
        //                                                 decimal_number(30, 31)
        //                                             ])
        //                                         ])
        //                                     ])
        //                                 ])
        //                             ])
        //                         ])
        //                     ]),
        //                     identifier(33, 36)
        //                 ])
        //             ])
        //         ]
        //     };
        // }

        #[test]
        fn parse_invalid_identifier_because_keyword() {
            fails_with! {
                parser: ZoKratesParser,
                input: "def",
                rule: Rule::identifier,
                positives: vec![Rule::identifier],
                negatives: vec![],
                pos: 0
            };
        }

        #[test]
        fn parse_for_loop() {
            let input = "for u32 i in 0..3 { c = c + a[i]; }";

            let parse = ZoKratesParser::parse(Rule::iteration_statement, input);
            assert!(parse.is_ok());
        }
    }
}
