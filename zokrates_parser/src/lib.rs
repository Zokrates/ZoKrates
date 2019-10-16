extern crate pest;
#[macro_use]
extern crate pest_derive;

use pest::error::Error;
use pest::iterators::Pairs;
use pest::Parser;

#[derive(Parser)]
#[grammar = "zokrates.pest"]
struct ZoKratesParser;

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
        #[test]
        fn parse_valid_identifier() {
            parses_to! {
                parser: ZoKratesParser,
                input: "valididentifier_01",
                rule: Rule::identifier,
                tokens: [
                    identifier(0, 18)
                ]
            };
        }

        #[test]
        fn parse_parameter_list() {
            parses_to! {
                parser: ZoKratesParser,
                input: "def foo(field a) -> (field, field): return 1
                ",
                rule: Rule::function_definition,
                tokens: [
                    function_definition(0, 45, [
                        identifier(4, 7),
                        // parameter_list is not created (silent rule)
                        parameter(8, 15, [
                            ty(8, 13, [
                                ty_basic(8, 13, [
                                    ty_field(8, 13)
                                ])
                            ]),
                            identifier(14, 15)
                        ]),
                        // type_list is not created (silent rule)
                        ty(21, 26, [
                            ty_basic(21, 26, [
                                ty_field(21, 26)
                            ])
                        ]),
                        ty(28, 33, [
                            ty_basic(28, 33, [
                                ty_field(28, 33)
                            ])
                        ]),
                        statement(36, 45, [
                            return_statement(36, 44, [
                                expression(43, 44, [
                                    term(43, 44, [
                                        primary_expression(43, 44, [
                                            constant(43, 44, [
                                                decimal_number(43, 44)
                                            ])
                                        ])
                                    ])
                                ])
                            ])
                        ])
                    ])
                ]
            };
        }

        #[test]
        fn parse_single_def_to_multi() {
            parses_to! {
                parser: ZoKratesParser,
                input: r#"a = foo()
            "#,
                rule: Rule::statement,
                tokens: [
                    statement(0, 22, [
                        multi_assignment_statement(0, 9, [
                            optionally_typed_identifier(0, 1, [
                                identifier(0, 1)
                            ]),
                            identifier(4, 7),
                        ])
                    ])
                ]
            };
        }

        #[test]
        fn parse_invalid_identifier() {
            fails_with! {
                parser: ZoKratesParser,
                input: "0_invalididentifier",
                rule: Rule::identifier,
                positives: vec![Rule::identifier],
                negatives: vec![],
                pos: 0
            };
        }

        #[test]
        fn parse_struct_def() {
            parses_to! {
                parser: ZoKratesParser,
                input: "struct Foo { field foo\n field[2] bar }
                ",
                rule: Rule::ty_struct_definition,
                tokens: [
                    ty_struct_definition(0, 39, [
                        identifier(7, 10),
                        struct_field(13, 22, [
                            ty(13, 18, [
                                ty_basic(13, 18, [
                                    ty_field(13, 18)
                                ])
                            ]),
                            identifier(19, 22)
                        ]),
                        struct_field(24, 36, [
                            ty(24, 33, [
                                ty_array(24, 33, [
                                    ty_basic_or_struct(24, 29, [
                                        ty_basic(24, 29, [
                                            ty_field(24, 29)
                                        ])
                                    ]),
                                    expression(30, 31, [
                                        term(30, 31, [
                                            primary_expression(30, 31, [
                                                constant(30, 31, [
                                                    decimal_number(30, 31)
                                                ])
                                            ])
                                        ])
                                    ])
                                ])
                            ]),
                            identifier(33, 36)
                        ])
                    ])
                ]
            };
        }

        #[test]
        fn parse_invalid_identifier_because_keyword() {
            fails_with! {
                parser: ZoKratesParser,
                input: "endfor",
                rule: Rule::identifier,
                positives: vec![Rule::identifier],
                negatives: vec![],
                pos: 0
            };
        }

        #[test]
        fn parse_for_loop() {
            let input = "for field i in 0..3 do \n c = c + a[i] \n endfor";

            let parse = ZoKratesParser::parse(Rule::iteration_statement, input);
            assert!(parse.is_ok());
        }
    }
}
