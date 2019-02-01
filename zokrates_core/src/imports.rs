//! Module containing structs and enums to represent imports.
//!
//! @file imports.rs
//! @author Thibaut Schaeffer <thibaut@schaeff.fr>
//! @date 2018

use absy::*;
use compile::compile_aux;
use compile::{CompileErrorInner, CompileErrors};
use flat_absy::*;
use parser::Position;
use std::fmt;
use std::io;
use std::io::BufRead;
use zokrates_field::field::Field;

pub struct CompiledImport<T: Field> {
    pub flat_func: FlatFunction<T>,
}

impl<T: Field> CompiledImport<T> {
    fn new(prog: FlatProg<T>, alias: String) -> CompiledImport<T> {
        match prog.functions.iter().find(|fun| fun.id == "main") {
            Some(fun) => CompiledImport {
                flat_func: FlatFunction {
                    id: alias,
                    ..fun.clone()
                },
            },
            None => panic!("no main"),
        }
    }
}

#[derive(PartialEq, Debug)]
pub struct Error {
    pos: Option<(Position, Position)>,
    message: String,
}

impl Error {
    pub fn new<T: Into<String>>(message: T) -> Error {
        Error {
            pos: None,
            message: message.into(),
        }
    }

    fn with_pos(self, pos: Option<(Position, Position)>) -> Error {
        Error { pos, ..self }
    }
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let location = self
            .pos
            .map(|p| format!("{}", p.0))
            .unwrap_or("?".to_string());
        write!(f, "{}\n\t{}", location, self.message)
    }
}

impl From<io::Error> for Error {
    fn from(error: io::Error) -> Self {
        Error {
            pos: None,
            message: format!("I/O Error: {}", error),
        }
    }
}

#[derive(PartialEq, Clone, Serialize, Deserialize)]
pub struct Import {
    source: String,
    alias: Option<String>,
}

pub type ImportNode = Node<Import>;

impl Import {
    pub fn new(source: String) -> Import {
        Import {
            source: source,
            alias: None,
        }
    }

    pub fn get_alias(&self) -> &Option<String> {
        &self.alias
    }

    pub fn new_with_alias(source: String, alias: &String) -> Import {
        Import {
            source: source,
            alias: Some(alias.clone()),
        }
    }

    pub fn get_source(&self) -> &String {
        &self.source
    }
}

impl fmt::Display for Import {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self.alias {
            Some(ref alias) => write!(f, "import {} as {}", self.source, alias),
            None => write!(f, "import {}", self.source),
        }
    }
}

impl fmt::Debug for Import {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self.alias {
            Some(ref alias) => write!(f, "import(source: {}, alias: {})", self.source, alias),
            None => write!(f, "import(source: {})", self.source),
        }
    }
}

pub struct Importer {}

impl Importer {
    pub fn new() -> Importer {
        Importer {}
    }

    pub fn apply_imports<T: Field, S: BufRead, E: Into<Error>>(
        &self,
        destination: Prog<T>,
        location: Option<String>,
        resolve_option: Option<fn(&Option<String>, &String) -> Result<(S, String, String), E>>,
    ) -> Result<Prog<T>, CompileErrors<T>> {
        let mut origins: Vec<CompiledImport<T>> = vec![];

        for import in destination.imports.iter() {
            let pos = import.pos();
            let import = &import.value;
            // handle the case of special libsnark and packing imports
            if import.source.starts_with("LIBSNARK") {
                #[cfg(feature = "libsnark")]
                {
                    use helpers::LibsnarkGadgetHelper;
                    use libsnark::{get_ethsha256_constraints, get_sha256_constraints};
                    use serde_json::from_str;
                    use standard::{DirectiveR1CS, R1CS};
                    use std::io::BufReader;

                    match import.source.as_ref() {
                        "LIBSNARK/sha256" => {
                            let r1cs: R1CS = from_str(&get_ethsha256_constraints()).unwrap();
                            let dr1cs: DirectiveR1CS = DirectiveR1CS {
                                r1cs,
                                directive: LibsnarkGadgetHelper::Sha256Ethereum,
                            };
                            let compiled = FlatProg::from(dr1cs);
                            let alias = match import.alias {
                                Some(ref alias) => alias.clone(),
                                None => String::from("sha256"),
                            };
                            origins.push(CompiledImport::new(compiled, alias));
                        }
                        "LIBSNARK/sha256compression" => {
                            let r1cs: R1CS = from_str(&get_sha256_constraints()).unwrap();
                            let dr1cs: DirectiveR1CS = DirectiveR1CS {
                                r1cs,
                                directive: LibsnarkGadgetHelper::Sha256Compress,
                            };
                            let compiled = FlatProg::from(dr1cs);
                            let alias = match import.alias {
                                Some(ref alias) => alias.clone(),
                                None => String::from("sha256compression"),
                            };
                            origins.push(CompiledImport::new(compiled, alias));
                        }
                        "LIBSNARK/sha256packed" => {
                            let source = sha_packed_typed();
                            let mut reader = BufReader::new(source.as_bytes());
                            let compiled = compile_aux(
                                &mut reader,
                                None::<String>,
                                None::<
                                    fn(&Option<String>, &String) -> Result<(S, String, String), E>,
                                >,
                            )?;
                            let alias = match import.alias {
                                Some(ref alias) => alias.clone(),
                                None => String::from("sha256packed"),
                            };
                            origins.push(CompiledImport::new(compiled, alias));
                        }
                        s => {
                            return Err(CompileErrorInner::ImportError(
                                Error::new(format!("Gadget {} not found", s)).with_pos(Some(pos)),
                            )
                            .with_context(&location)
                            .into());
                        }
                    }
                }
                #[cfg(not(feature = "libsnark"))]
                {
                    panic!("libsnark is not enabled, cannot access {}", import.source)
                }
            } else if import.source.starts_with("PACKING") {
                use types::conversions::{pack, unpack};

                match import.source.as_ref() {
                    "PACKING/pack128" => {
                        let compiled = pack(128);
                        let alias = match import.alias {
                            Some(ref alias) => alias.clone(),
                            None => String::from("pack128"),
                        };
                        origins.push(CompiledImport::new(compiled, alias));
                    }
                    "PACKING/unpack128" => {
                        let compiled = unpack(128);
                        let alias = match import.alias {
                            Some(ref alias) => alias.clone(),
                            None => String::from("unpack128"),
                        };
                        origins.push(CompiledImport::new(compiled, alias));
                    }
                    s => {
                        return Err(CompileErrorInner::ImportError(
                            Error::new(format!("Packing helper {} not found", s))
                                .with_pos(Some(pos)),
                        )
                        .with_context(&location)
                        .into());
                    }
                }
            } else {
                // to resolve imports, we need a resolver
                match resolve_option {
                    Some(resolve) => match resolve(&location, &import.source) {
                        Ok((mut reader, location, auto_alias)) => {
                            let compiled = compile_aux(&mut reader, Some(location), resolve_option)
                                .map_err(|e| e.with_context(Some(import.source.clone())))?;
                            let alias = match import.alias {
                                Some(ref alias) => alias.clone(),
                                None => auto_alias,
                            };
                            origins.push(CompiledImport::new(compiled, alias));
                        }
                        Err(err) => {
                            return Err(CompileErrorInner::ImportError(
                                err.into().with_pos(Some(pos)),
                            )
                            .with_context(&location)
                            .into());
                        }
                    },
                    None => {
                        return Err(CompileErrorInner::from(Error::new(
                            "Can't resolve import without a resolver",
                        ))
                        .with_context(&location)
                        .into());
                    }
                }
            }
        }

        Ok(Prog {
            imports: vec![],
            functions: destination.clone().functions,
            imported_functions: origins.into_iter().map(|o| o.flat_func).collect(),
        })
    }
}

#[cfg(feature = "libsnark")]
fn sha_packed_typed() -> String {
    String::from(r#"
	import "PACKING/pack128"
	import "PACKING/unpack128"
	import "LIBSNARK/sha256"

	def main(field a, field b, field c, field d) -> (field, field):
		a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23, a24, a25, a26, a27, a28, a29, a30, a31, a32, a33, a34, a35, a36, a37, a38, a39, a40, a41, a42, a43, a44, a45, a46, a47, a48, a49, a50, a51, a52, a53, a54, a55, a56, a57, a58, a59, a60, a61, a62, a63, a64, a65, a66, a67, a68, a69, a70, a71, a72, a73, a74, a75, a76, a77, a78, a79, a80, a81, a82, a83, a84, a85, a86, a87, a88, a89, a90, a91, a92, a93, a94, a95, a96, a97, a98, a99, a100, a101, a102, a103, a104, a105, a106, a107, a108, a109, a110, a111, a112, a113, a114, a115, a116, a117, a118, a119, a120, a121, a122, a123, a124, a125, a126, a127 = unpack128(a)
		b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32, b33, b34, b35, b36, b37, b38, b39, b40, b41, b42, b43, b44, b45, b46, b47, b48, b49, b50, b51, b52, b53, b54, b55, b56, b57, b58, b59, b60, b61, b62, b63, b64, b65, b66, b67, b68, b69, b70, b71, b72, b73, b74, b75, b76, b77, b78, b79, b80, b81, b82, b83, b84, b85, b86, b87, b88, b89, b90, b91, b92, b93, b94, b95, b96, b97, b98, b99, b100, b101, b102, b103, b104, b105, b106, b107, b108, b109, b110, b111, b112, b113, b114, b115, b116, b117, b118, b119, b120, b121, b122, b123, b124, b125, b126, b127 = unpack128(b)
		c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18, c19, c20, c21, c22, c23, c24, c25, c26, c27, c28, c29, c30, c31, c32, c33, c34, c35, c36, c37, c38, c39, c40, c41, c42, c43, c44, c45, c46, c47, c48, c49, c50, c51, c52, c53, c54, c55, c56, c57, c58, c59, c60, c61, c62, c63, c64, c65, c66, c67, c68, c69, c70, c71, c72, c73, c74, c75, c76, c77, c78, c79, c80, c81, c82, c83, c84, c85, c86, c87, c88, c89, c90, c91, c92, c93, c94, c95, c96, c97, c98, c99, c100, c101, c102, c103, c104, c105, c106, c107, c108, c109, c110, c111, c112, c113, c114, c115, c116, c117, c118, c119, c120, c121, c122, c123, c124, c125, c126, c127 = unpack128(c)
		d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20, d21, d22, d23, d24, d25, d26, d27, d28, d29, d30, d31, d32, d33, d34, d35, d36, d37, d38, d39, d40, d41, d42, d43, d44, d45, d46, d47, d48, d49, d50, d51, d52, d53, d54, d55, d56, d57, d58, d59, d60, d61, d62, d63, d64, d65, d66, d67, d68, d69, d70, d71, d72, d73, d74, d75, d76, d77, d78, d79, d80, d81, d82, d83, d84, d85, d86, d87, d88, d89, d90, d91, d92, d93, d94, d95, d96, d97, d98, d99, d100, d101, d102, d103, d104, d105, d106, d107, d108, d109, d110, d111, d112, d113, d114, d115, d116, d117, d118, d119, d120, d121, d122, d123, d124, d125, d126, d127 = unpack128(d)

		hashed0, hashed1, hashed2, hashed3, hashed4, hashed5, hashed6, hashed7, hashed8, hashed9, hashed10, hashed11, hashed12, hashed13, hashed14, hashed15, hashed16, hashed17, hashed18, hashed19, hashed20, hashed21, hashed22, hashed23, hashed24, hashed25, hashed26, hashed27, hashed28, hashed29, hashed30, hashed31, hashed32, hashed33, hashed34, hashed35, hashed36, hashed37, hashed38, hashed39, hashed40, hashed41, hashed42, hashed43, hashed44, hashed45, hashed46, hashed47, hashed48, hashed49, hashed50, hashed51, hashed52, hashed53, hashed54, hashed55, hashed56, hashed57, hashed58, hashed59, hashed60, hashed61, hashed62, hashed63, hashed64, hashed65, hashed66, hashed67, hashed68, hashed69, hashed70, hashed71, hashed72, hashed73, hashed74, hashed75, hashed76, hashed77, hashed78, hashed79, hashed80, hashed81, hashed82, hashed83, hashed84, hashed85, hashed86, hashed87, hashed88, hashed89, hashed90, hashed91, hashed92, hashed93, hashed94, hashed95, hashed96, hashed97, hashed98, hashed99, hashed100, hashed101, hashed102, hashed103, hashed104, hashed105, hashed106, hashed107, hashed108, hashed109, hashed110, hashed111, hashed112, hashed113, hashed114, hashed115, hashed116, hashed117, hashed118, hashed119, hashed120, hashed121, hashed122, hashed123, hashed124, hashed125, hashed126, hashed127, hashed128, hashed129, hashed130, hashed131, hashed132, hashed133, hashed134, hashed135, hashed136, hashed137, hashed138, hashed139, hashed140, hashed141, hashed142, hashed143, hashed144, hashed145, hashed146, hashed147, hashed148, hashed149, hashed150, hashed151, hashed152, hashed153, hashed154, hashed155, hashed156, hashed157, hashed158, hashed159, hashed160, hashed161, hashed162, hashed163, hashed164, hashed165, hashed166, hashed167, hashed168, hashed169, hashed170, hashed171, hashed172, hashed173, hashed174, hashed175, hashed176, hashed177, hashed178, hashed179, hashed180, hashed181, hashed182, hashed183, hashed184, hashed185, hashed186, hashed187, hashed188, hashed189, hashed190, hashed191, hashed192, hashed193, hashed194, hashed195, hashed196, hashed197, hashed198, hashed199, hashed200, hashed201, hashed202, hashed203, hashed204, hashed205, hashed206, hashed207, hashed208, hashed209, hashed210, hashed211, hashed212, hashed213, hashed214, hashed215, hashed216, hashed217, hashed218, hashed219, hashed220, hashed221, hashed222, hashed223, hashed224, hashed225, hashed226, hashed227, hashed228, hashed229, hashed230, hashed231, hashed232, hashed233, hashed234, hashed235, hashed236, hashed237, hashed238, hashed239, hashed240, hashed241, hashed242, hashed243, hashed244, hashed245, hashed246, hashed247, hashed248, hashed249, hashed250, hashed251, hashed252, hashed253, hashed254, hashed255 = sha256(a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23, a24, a25, a26, a27, a28, a29, a30, a31, a32, a33, a34, a35, a36, a37, a38, a39, a40, a41, a42, a43, a44, a45, a46, a47, a48, a49, a50, a51, a52, a53, a54, a55, a56, a57, a58, a59, a60, a61, a62, a63, a64, a65, a66, a67, a68, a69, a70, a71, a72, a73, a74, a75, a76, a77, a78, a79, a80, a81, a82, a83, a84, a85, a86, a87, a88, a89, a90, a91, a92, a93, a94, a95, a96, a97, a98, a99, a100, a101, a102, a103, a104, a105, a106, a107, a108, a109, a110, a111, a112, a113, a114, a115, a116, a117, a118, a119, a120, a121, a122, a123, a124, a125, a126, a127, b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32, b33, b34, b35, b36, b37, b38, b39, b40, b41, b42, b43, b44, b45, b46, b47, b48, b49, b50, b51, b52, b53, b54, b55, b56, b57, b58, b59, b60, b61, b62, b63, b64, b65, b66, b67, b68, b69, b70, b71, b72, b73, b74, b75, b76, b77, b78, b79, b80, b81, b82, b83, b84, b85, b86, b87, b88, b89, b90, b91, b92, b93, b94, b95, b96, b97, b98, b99, b100, b101, b102, b103, b104, b105, b106, b107, b108, b109, b110, b111, b112, b113, b114, b115, b116, b117, b118, b119, b120, b121, b122, b123, b124, b125, b126, b127, c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18, c19, c20, c21, c22, c23, c24, c25, c26, c27, c28, c29, c30, c31, c32, c33, c34, c35, c36, c37, c38, c39, c40, c41, c42, c43, c44, c45, c46, c47, c48, c49, c50, c51, c52, c53, c54, c55, c56, c57, c58, c59, c60, c61, c62, c63, c64, c65, c66, c67, c68, c69, c70, c71, c72, c73, c74, c75, c76, c77, c78, c79, c80, c81, c82, c83, c84, c85, c86, c87, c88, c89, c90, c91, c92, c93, c94, c95, c96, c97, c98, c99, c100, c101, c102, c103, c104, c105, c106, c107, c108, c109, c110, c111, c112, c113, c114, c115, c116, c117, c118, c119, c120, c121, c122, c123, c124, c125, c126, c127, d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20, d21, d22, d23, d24, d25, d26, d27, d28, d29, d30, d31, d32, d33, d34, d35, d36, d37, d38, d39, d40, d41, d42, d43, d44, d45, d46, d47, d48, d49, d50, d51, d52, d53, d54, d55, d56, d57, d58, d59, d60, d61, d62, d63, d64, d65, d66, d67, d68, d69, d70, d71, d72, d73, d74, d75, d76, d77, d78, d79, d80, d81, d82, d83, d84, d85, d86, d87, d88, d89, d90, d91, d92, d93, d94, d95, d96, d97, d98, d99, d100, d101, d102, d103, d104, d105, d106, d107, d108, d109, d110, d111, d112, d113, d114, d115, d116, d117, d118, d119, d120, d121, d122, d123, d124, d125, d126, d127)
		
		res0 = pack128(hashed0, hashed1, hashed2, hashed3, hashed4, hashed5, hashed6, hashed7, hashed8, hashed9, hashed10, hashed11, hashed12, hashed13, hashed14, hashed15, hashed16, hashed17, hashed18, hashed19, hashed20, hashed21, hashed22, hashed23, hashed24, hashed25, hashed26, hashed27, hashed28, hashed29, hashed30, hashed31, hashed32, hashed33, hashed34, hashed35, hashed36, hashed37, hashed38, hashed39, hashed40, hashed41, hashed42, hashed43, hashed44, hashed45, hashed46, hashed47, hashed48, hashed49, hashed50, hashed51, hashed52, hashed53, hashed54, hashed55, hashed56, hashed57, hashed58, hashed59, hashed60, hashed61, hashed62, hashed63, hashed64, hashed65, hashed66, hashed67, hashed68, hashed69, hashed70, hashed71, hashed72, hashed73, hashed74, hashed75, hashed76, hashed77, hashed78, hashed79, hashed80, hashed81, hashed82, hashed83, hashed84, hashed85, hashed86, hashed87, hashed88, hashed89, hashed90, hashed91, hashed92, hashed93, hashed94, hashed95, hashed96, hashed97, hashed98, hashed99, hashed100, hashed101, hashed102, hashed103, hashed104, hashed105, hashed106, hashed107, hashed108, hashed109, hashed110, hashed111, hashed112, hashed113, hashed114, hashed115, hashed116, hashed117, hashed118, hashed119, hashed120, hashed121, hashed122, hashed123, hashed124, hashed125, hashed126, hashed127)
		res1 = pack128(hashed128, hashed129, hashed130, hashed131, hashed132, hashed133, hashed134, hashed135, hashed136, hashed137, hashed138, hashed139, hashed140, hashed141, hashed142, hashed143, hashed144, hashed145, hashed146, hashed147, hashed148, hashed149, hashed150, hashed151, hashed152, hashed153, hashed154, hashed155, hashed156, hashed157, hashed158, hashed159, hashed160, hashed161, hashed162, hashed163, hashed164, hashed165, hashed166, hashed167, hashed168, hashed169, hashed170, hashed171, hashed172, hashed173, hashed174, hashed175, hashed176, hashed177, hashed178, hashed179, hashed180, hashed181, hashed182, hashed183, hashed184, hashed185, hashed186, hashed187, hashed188, hashed189, hashed190, hashed191, hashed192, hashed193, hashed194, hashed195, hashed196, hashed197, hashed198, hashed199, hashed200, hashed201, hashed202, hashed203, hashed204, hashed205, hashed206, hashed207, hashed208, hashed209, hashed210, hashed211, hashed212, hashed213, hashed214, hashed215, hashed216, hashed217, hashed218, hashed219, hashed220, hashed221, hashed222, hashed223, hashed224, hashed225, hashed226, hashed227, hashed228, hashed229, hashed230, hashed231, hashed232, hashed233, hashed234, hashed235, hashed236, hashed237, hashed238, hashed239, hashed240, hashed241, hashed242, hashed243, hashed244, hashed245, hashed246, hashed247, hashed248, hashed249, hashed250, hashed251, hashed252, hashed253, hashed254, hashed255)

		return res0, res1
	"#)
}

#[cfg(test)]
mod tests {

    use super::*;

    #[test]
    fn create_with_no_alias() {
        assert_eq!(
            Import::new("./foo/bar/baz.code".to_string()),
            Import {
                source: String::from("./foo/bar/baz.code"),
                alias: None,
            }
        );
    }

    #[test]
    fn create_with_alias() {
        assert_eq!(
            Import::new_with_alias("./foo/bar/baz.code".to_string(), &"myalias".to_string()),
            Import {
                source: String::from("./foo/bar/baz.code"),
                alias: Some("myalias".to_string()),
            }
        );
    }
}
