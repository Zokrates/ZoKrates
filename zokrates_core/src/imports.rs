//! Module containing structs and enums to represent imports.
//!
//! @file imports.rs
//! @author Thibaut Schaeffer <thibaut@schaeff.fr>
//! @date 2018

use compile::CompileError;
use std::io::BufRead;
use compile::compile_aux;
use std::fmt;
use absy::*;
use flat_absy::*;
use field::Field;
use std::io;

pub struct CompiledImport<T: Field> {
	pub flat_func: FlatFunction<T>,
}

impl<T: Field> CompiledImport<T> {
	fn new(prog: FlatProg<T>, alias: String) -> CompiledImport<T> {
                match prog.functions.iter().find(|fun| fun.id == "main") {
                        Some(fun) => {
                                CompiledImport { flat_func:
                                        FlatFunction {
                                            id: alias,
                                            ..fun.clone()
                                        }
                                }
                        },
                        None => panic!("no main")
                }
        }
}

#[derive(PartialEq, Debug)]
pub struct Error {
	message: String
}

impl Error {
	pub fn new<T: Into<String>>(message: T) -> Error {
		Error {
			message: message.into()
		}
	}
}

impl fmt::Display for Error {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		write!(f, "{}", self.message)
	}
}

impl From<io::Error> for Error {
	fn from(error: io::Error) -> Self {
		Error {
			message: format!("I/O Error: {:?}", error)
		}
	}
}

#[derive(PartialEq, Clone, Serialize, Deserialize)]
pub struct Import {
	source: String,
	alias: Option<String>,
}

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
			Some(ref alias) => {
				write!(f, "import {} as {}", self.source, alias)
			},
			None => {
				write!(f, "import {}", self.source)
			}
		}
	}
}

impl fmt::Debug for Import {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    	match self.alias {
			Some(ref alias) => {
				write!(f, "import(source: {}, alias: {})", self.source, alias)
			},
			None => {
				write!(f, "import(source: {})", self.source)
			}
	    }
	}
}

pub struct Importer {

}

impl Importer {
	pub fn new() -> Importer {
		Importer {

		}
	}

	pub	fn apply_imports<T: Field, S: BufRead, E: Into<Error>>(&self, destination: Prog<T>, location: Option<String>, resolve_option: Option<fn(&Option<String>, &String) -> Result<(S, String, String), E>>) -> Result<Prog<T>, CompileError<T>> {

		let mut origins: Vec<CompiledImport<T>> = vec![];

    	for import in destination.imports.iter() {
    		// handle the case of special libsnark and packing imports
    		if import.source.starts_with("LIBSNARK") {
    			#[cfg(feature = "libsnark")]
    			{
    				use libsnark::{get_sha256_constraints, get_ethsha256_constraints};
			    	use standard::{R1CS, DirectiveR1CS};
			    	use serde_json::from_str;
					use helpers::LibsnarkGadgetHelper;
					use std::io::BufReader;

	    			match import.source.as_ref() {
	    				"LIBSNARK/sha256" => {
	    					let r1cs: R1CS = from_str(&get_ethsha256_constraints()).unwrap();
						    let dr1cs : DirectiveR1CS = DirectiveR1CS { r1cs, directive : LibsnarkGadgetHelper::Sha256Ethereum };
						    let compiled = FlatProg::from(dr1cs);
						    let alias = match import.alias {
				    			Some(ref alias) => alias.clone(),
				    			None => String::from("sha256")
				    		};
					    	origins.push(CompiledImport::new(compiled, alias));
	    				},
	    				"LIBSNARK/sha256compression" => {
	    					let r1cs: R1CS = from_str(&get_sha256_constraints()).unwrap();
						    let dr1cs : DirectiveR1CS = DirectiveR1CS { r1cs, directive : LibsnarkGadgetHelper::Sha256Compress };
						    let compiled = FlatProg::from(dr1cs);
						    let alias = match import.alias {
				    			Some(ref alias) => alias.clone(),
				    			None => String::from("sha256compression")
				    		};
					    	origins.push(CompiledImport::new(compiled, alias));
	    				},
	    				"LIBSNARK/sha256packed" => {
	    					let source = sha_packed_typed();
	    					let mut reader = BufReader::new(source.as_bytes());
	    					let compiled = compile_aux(
	    						&mut reader,
	    						None::<String>,
	    						None::<fn(&Option<String>, &String) -> Result<(S, String, String), E>>
	    					)?;
				    		let alias = match import.alias {
				    			Some(ref alias) => alias.clone(),
				    			None => String::from("sha256packed")
				    		};
					    	origins.push(CompiledImport::new(compiled, alias));
	    				},
	    				s => return Err(CompileError::ImportError(Error::new(format!("Gadget {} not found", s))))
	    			}
    			}
    		} else if import.source.starts_with("PACKING") {
				use types::conversions::{pack, unpack};

    			match import.source.as_ref() {
    				"PACKING/pack254" => {
					    let compiled = pack(254);
					    let alias = match import.alias {
			    			Some(ref alias) => alias.clone(),
			    			None => String::from("pack254")
			    		};
				    	origins.push(CompiledImport::new(compiled, alias));
    				},
    				"PACKING/unpack254" => {
					    let compiled = unpack(254);
					    let alias = match import.alias {
			    			Some(ref alias) => alias.clone(),
			    			None => String::from("unpack254")
			    		};
				    	origins.push(CompiledImport::new(compiled, alias));
    				},
    				s => return Err(CompileError::ImportError(Error::new(format!("Packing helper {} not found", s))))
    			}
    		} else {
    			// to resolve imports, we need a resolver
			    match resolve_option {
			    	Some(resolve) => {
			    		match resolve(&location, &import.source) {
			    			Ok((mut reader, location, auto_alias)) => {
					    		let compiled = compile_aux(&mut reader, Some(location), resolve_option)?;
					    		let alias = match import.alias {
					    			Some(ref alias) => alias.clone(),
					    			None => auto_alias
					    		};
						    	origins.push(CompiledImport::new(compiled, alias));
					    	},
			    			Err(err) => return Err(CompileError::ImportError(err.into()))
			    		}
			    	}
			    	None => {
			    		return Err(Error::new("Can't resolve import without a resolver").into())
			    	}
			    }
    		}
    	}
	  
		Ok(Prog {
			imports: vec![],
			functions: destination.clone().functions,
			imported_functions: origins.into_iter().map(|o| o.flat_func).collect()
		})
	}
}

#[cfg(feature = "libsnark")]
fn sha_packed_typed() -> String {
	String::from(r#"
	import "PACKING/pack254"
	import "PACKING/unpack254"
	import "LIBSNARK/sha256"

	def main(field a, field b) -> (field):
		field a0 = 0
		field a1 = 0
		field a2, field a3, field a4, field a5, field a6, field a7, field a8, field a9, field a10, field a11, field a12, field a13, field a14, field a15, field a16, field a17, field a18, field a19, field a20, field a21, field a22, field a23, field a24, field a25, field a26, field a27, field a28, field a29, field a30, field a31, field a32, field a33, field a34, field a35, field a36, field a37, field a38, field a39, field a40, field a41, field a42, field a43, field a44, field a45, field a46, field a47, field a48, field a49, field a50, field a51, field a52, field a53, field a54, field a55, field a56, field a57, field a58, field a59, field a60, field a61, field a62, field a63, field a64, field a65, field a66, field a67, field a68, field a69, field a70, field a71, field a72, field a73, field a74, field a75, field a76, field a77, field a78, field a79, field a80, field a81, field a82, field a83, field a84, field a85, field a86, field a87, field a88, field a89, field a90, field a91, field a92, field a93, field a94, field a95, field a96, field a97, field a98, field a99, field a100, field a101, field a102, field a103, field a104, field a105, field a106, field a107, field a108, field a109, field a110, field a111, field a112, field a113, field a114, field a115, field a116, field a117, field a118, field a119, field a120, field a121, field a122, field a123, field a124, field a125, field a126, field a127, field a128, field a129, field a130, field a131, field a132, field a133, field a134, field a135, field a136, field a137, field a138, field a139, field a140, field a141, field a142, field a143, field a144, field a145, field a146, field a147, field a148, field a149, field a150, field a151, field a152, field a153, field a154, field a155, field a156, field a157, field a158, field a159, field a160, field a161, field a162, field a163, field a164, field a165, field a166, field a167, field a168, field a169, field a170, field a171, field a172, field a173, field a174, field a175, field a176, field a177, field a178, field a179, field a180, field a181, field a182, field a183, field a184, field a185, field a186, field a187, field a188, field a189, field a190, field a191, field a192, field a193, field a194, field a195, field a196, field a197, field a198, field a199, field a200, field a201, field a202, field a203, field a204, field a205, field a206, field a207, field a208, field a209, field a210, field a211, field a212, field a213, field a214, field a215, field a216, field a217, field a218, field a219, field a220, field a221, field a222, field a223, field a224, field a225, field a226, field a227, field a228, field a229, field a230, field a231, field a232, field a233, field a234, field a235, field a236, field a237, field a238, field a239, field a240, field a241, field a242, field a243, field a244, field a245, field a246, field a247, field a248, field a249, field a250, field a251, field a252, field a253, field a254, field a255 = unpack254(a)
		field b0 = 0
		field b1 = 0
		field b2, field b3, field b4, field b5, field b6, field b7, field b8, field b9, field b10, field b11, field b12, field b13, field b14, field b15, field b16, field b17, field b18, field b19, field b20, field b21, field b22, field b23, field b24, field b25, field b26, field b27, field b28, field b29, field b30, field b31, field b32, field b33, field b34, field b35, field b36, field b37, field b38, field b39, field b40, field b41, field b42, field b43, field b44, field b45, field b46, field b47, field b48, field b49, field b50, field b51, field b52, field b53, field b54, field b55, field b56, field b57, field b58, field b59, field b60, field b61, field b62, field b63, field b64, field b65, field b66, field b67, field b68, field b69, field b70, field b71, field b72, field b73, field b74, field b75, field b76, field b77, field b78, field b79, field b80, field b81, field b82, field b83, field b84, field b85, field b86, field b87, field b88, field b89, field b90, field b91, field b92, field b93, field b94, field b95, field b96, field b97, field b98, field b99, field b100, field b101, field b102, field b103, field b104, field b105, field b106, field b107, field b108, field b109, field b110, field b111, field b112, field b113, field b114, field b115, field b116, field b117, field b118, field b119, field b120, field b121, field b122, field b123, field b124, field b125, field b126, field b127, field b128, field b129, field b130, field b131, field b132, field b133, field b134, field b135, field b136, field b137, field b138, field b139, field b140, field b141, field b142, field b143, field b144, field b145, field b146, field b147, field b148, field b149, field b150, field b151, field b152, field b153, field b154, field b155, field b156, field b157, field b158, field b159, field b160, field b161, field b162, field b163, field b164, field b165, field b166, field b167, field b168, field b169, field b170, field b171, field b172, field b173, field b174, field b175, field b176, field b177, field b178, field b179, field b180, field b181, field b182, field b183, field b184, field b185, field b186, field b187, field b188, field b189, field b190, field b191, field b192, field b193, field b194, field b195, field b196, field b197, field b198, field b199, field b200, field b201, field b202, field b203, field b204, field b205, field b206, field b207, field b208, field b209, field b210, field b211, field b212, field b213, field b214, field b215, field b216, field b217, field b218, field b219, field b220, field b221, field b222, field b223, field b224, field b225, field b226, field b227, field b228, field b229, field b230, field b231, field b232, field b233, field b234, field b235, field b236, field b237, field b238, field b239, field b240, field b241, field b242, field b243, field b244, field b245, field b246, field b247, field b248, field b249, field b250, field b251, field b252, field b253, field b254, field b255 = unpack254(b)
		field hashed0, field hashed1, field hashed2, field hashed3, field hashed4, field hashed5, field hashed6, field hashed7, field hashed8, field hashed9, field hashed10, field hashed11, field hashed12, field hashed13, field hashed14, field hashed15, field hashed16, field hashed17, field hashed18, field hashed19, field hashed20, field hashed21, field hashed22, field hashed23, field hashed24, field hashed25, field hashed26, field hashed27, field hashed28, field hashed29, field hashed30, field hashed31, field hashed32, field hashed33, field hashed34, field hashed35, field hashed36, field hashed37, field hashed38, field hashed39, field hashed40, field hashed41, field hashed42, field hashed43, field hashed44, field hashed45, field hashed46, field hashed47, field hashed48, field hashed49, field hashed50, field hashed51, field hashed52, field hashed53, field hashed54, field hashed55, field hashed56, field hashed57, field hashed58, field hashed59, field hashed60, field hashed61, field hashed62, field hashed63, field hashed64, field hashed65, field hashed66, field hashed67, field hashed68, field hashed69, field hashed70, field hashed71, field hashed72, field hashed73, field hashed74, field hashed75, field hashed76, field hashed77, field hashed78, field hashed79, field hashed80, field hashed81, field hashed82, field hashed83, field hashed84, field hashed85, field hashed86, field hashed87, field hashed88, field hashed89, field hashed90, field hashed91, field hashed92, field hashed93, field hashed94, field hashed95, field hashed96, field hashed97, field hashed98, field hashed99, field hashed100, field hashed101, field hashed102, field hashed103, field hashed104, field hashed105, field hashed106, field hashed107, field hashed108, field hashed109, field hashed110, field hashed111, field hashed112, field hashed113, field hashed114, field hashed115, field hashed116, field hashed117, field hashed118, field hashed119, field hashed120, field hashed121, field hashed122, field hashed123, field hashed124, field hashed125, field hashed126, field hashed127, field hashed128, field hashed129, field hashed130, field hashed131, field hashed132, field hashed133, field hashed134, field hashed135, field hashed136, field hashed137, field hashed138, field hashed139, field hashed140, field hashed141, field hashed142, field hashed143, field hashed144, field hashed145, field hashed146, field hashed147, field hashed148, field hashed149, field hashed150, field hashed151, field hashed152, field hashed153, field hashed154, field hashed155, field hashed156, field hashed157, field hashed158, field hashed159, field hashed160, field hashed161, field hashed162, field hashed163, field hashed164, field hashed165, field hashed166, field hashed167, field hashed168, field hashed169, field hashed170, field hashed171, field hashed172, field hashed173, field hashed174, field hashed175, field hashed176, field hashed177, field hashed178, field hashed179, field hashed180, field hashed181, field hashed182, field hashed183, field hashed184, field hashed185, field hashed186, field hashed187, field hashed188, field hashed189, field hashed190, field hashed191, field hashed192, field hashed193, field hashed194, field hashed195, field hashed196, field hashed197, field hashed198, field hashed199, field hashed200, field hashed201, field hashed202, field hashed203, field hashed204, field hashed205, field hashed206, field hashed207, field hashed208, field hashed209, field hashed210, field hashed211, field hashed212, field hashed213, field hashed214, field hashed215, field hashed216, field hashed217, field hashed218, field hashed219, field hashed220, field hashed221, field hashed222, field hashed223, field hashed224, field hashed225, field hashed226, field hashed227, field hashed228, field hashed229, field hashed230, field hashed231, field hashed232, field hashed233, field hashed234, field hashed235, field hashed236, field hashed237, field hashed238, field hashed239, field hashed240, field hashed241, field hashed242, field hashed243, field hashed244, field hashed245, field hashed246, field hashed247, field hashed248, field hashed249, field hashed250, field hashed251, field hashed252, field hashed253, field hashed254, field hashed255 = sha256(a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23, a24, a25, a26, a27, a28, a29, a30, a31, a32, a33, a34, a35, a36, a37, a38, a39, a40, a41, a42, a43, a44, a45, a46, a47, a48, a49, a50, a51, a52, a53, a54, a55, a56, a57, a58, a59, a60, a61, a62, a63, a64, a65, a66, a67, a68, a69, a70, a71, a72, a73, a74, a75, a76, a77, a78, a79, a80, a81, a82, a83, a84, a85, a86, a87, a88, a89, a90, a91, a92, a93, a94, a95, a96, a97, a98, a99, a100, a101, a102, a103, a104, a105, a106, a107, a108, a109, a110, a111, a112, a113, a114, a115, a116, a117, a118, a119, a120, a121, a122, a123, a124, a125, a126, a127, a128, a129, a130, a131, a132, a133, a134, a135, a136, a137, a138, a139, a140, a141, a142, a143, a144, a145, a146, a147, a148, a149, a150, a151, a152, a153, a154, a155, a156, a157, a158, a159, a160, a161, a162, a163, a164, a165, a166, a167, a168, a169, a170, a171, a172, a173, a174, a175, a176, a177, a178, a179, a180, a181, a182, a183, a184, a185, a186, a187, a188, a189, a190, a191, a192, a193, a194, a195, a196, a197, a198, a199, a200, a201, a202, a203, a204, a205, a206, a207, a208, a209, a210, a211, a212, a213, a214, a215, a216, a217, a218, a219, a220, a221, a222, a223, a224, a225, a226, a227, a228, a229, a230, a231, a232, a233, a234, a235, a236, a237, a238, a239, a240, a241, a242, a243, a244, a245, a246, a247, a248, a249, a250, a251, a252, a253, a254, a255, b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32, b33, b34, b35, b36, b37, b38, b39, b40, b41, b42, b43, b44, b45, b46, b47, b48, b49, b50, b51, b52, b53, b54, b55, b56, b57, b58, b59, b60, b61, b62, b63, b64, b65, b66, b67, b68, b69, b70, b71, b72, b73, b74, b75, b76, b77, b78, b79, b80, b81, b82, b83, b84, b85, b86, b87, b88, b89, b90, b91, b92, b93, b94, b95, b96, b97, b98, b99, b100, b101, b102, b103, b104, b105, b106, b107, b108, b109, b110, b111, b112, b113, b114, b115, b116, b117, b118, b119, b120, b121, b122, b123, b124, b125, b126, b127, b128, b129, b130, b131, b132, b133, b134, b135, b136, b137, b138, b139, b140, b141, b142, b143, b144, b145, b146, b147, b148, b149, b150, b151, b152, b153, b154, b155, b156, b157, b158, b159, b160, b161, b162, b163, b164, b165, b166, b167, b168, b169, b170, b171, b172, b173, b174, b175, b176, b177, b178, b179, b180, b181, b182, b183, b184, b185, b186, b187, b188, b189, b190, b191, b192, b193, b194, b195, b196, b197, b198, b199, b200, b201, b202, b203, b204, b205, b206, b207, b208, b209, b210, b211, b212, b213, b214, b215, b216, b217, b218, b219, b220, b221, b222, b223, b224, b225, b226, b227, b228, b229, b230, b231, b232, b233, b234, b235, b236, b237, b238, b239, b240, b241, b242, b243, b244, b245, b246, b247, b248, b249, b250, b251, b252, b253, b254, b255)
		return pack254(hashed2, hashed3, hashed4, hashed5, hashed6, hashed7, hashed8, hashed9, hashed10, hashed11, hashed12, hashed13, hashed14, hashed15, hashed16, hashed17, hashed18, hashed19, hashed20, hashed21, hashed22, hashed23, hashed24, hashed25, hashed26, hashed27, hashed28, hashed29, hashed30, hashed31, hashed32, hashed33, hashed34, hashed35, hashed36, hashed37, hashed38, hashed39, hashed40, hashed41, hashed42, hashed43, hashed44, hashed45, hashed46, hashed47, hashed48, hashed49, hashed50, hashed51, hashed52, hashed53, hashed54, hashed55, hashed56, hashed57, hashed58, hashed59, hashed60, hashed61, hashed62, hashed63, hashed64, hashed65, hashed66, hashed67, hashed68, hashed69, hashed70, hashed71, hashed72, hashed73, hashed74, hashed75, hashed76, hashed77, hashed78, hashed79, hashed80, hashed81, hashed82, hashed83, hashed84, hashed85, hashed86, hashed87, hashed88, hashed89, hashed90, hashed91, hashed92, hashed93, hashed94, hashed95, hashed96, hashed97, hashed98, hashed99, hashed100, hashed101, hashed102, hashed103, hashed104, hashed105, hashed106, hashed107, hashed108, hashed109, hashed110, hashed111, hashed112, hashed113, hashed114, hashed115, hashed116, hashed117, hashed118, hashed119, hashed120, hashed121, hashed122, hashed123, hashed124, hashed125, hashed126, hashed127, hashed128, hashed129, hashed130, hashed131, hashed132, hashed133, hashed134, hashed135, hashed136, hashed137, hashed138, hashed139, hashed140, hashed141, hashed142, hashed143, hashed144, hashed145, hashed146, hashed147, hashed148, hashed149, hashed150, hashed151, hashed152, hashed153, hashed154, hashed155, hashed156, hashed157, hashed158, hashed159, hashed160, hashed161, hashed162, hashed163, hashed164, hashed165, hashed166, hashed167, hashed168, hashed169, hashed170, hashed171, hashed172, hashed173, hashed174, hashed175, hashed176, hashed177, hashed178, hashed179, hashed180, hashed181, hashed182, hashed183, hashed184, hashed185, hashed186, hashed187, hashed188, hashed189, hashed190, hashed191, hashed192, hashed193, hashed194, hashed195, hashed196, hashed197, hashed198, hashed199, hashed200, hashed201, hashed202, hashed203, hashed204, hashed205, hashed206, hashed207, hashed208, hashed209, hashed210, hashed211, hashed212, hashed213, hashed214, hashed215, hashed216, hashed217, hashed218, hashed219, hashed220, hashed221, hashed222, hashed223, hashed224, hashed225, hashed226, hashed227, hashed228, hashed229, hashed230, hashed231, hashed232, hashed233, hashed234, hashed235, hashed236, hashed237, hashed238, hashed239, hashed240, hashed241, hashed242, hashed243, hashed244, hashed245, hashed246, hashed247, hashed248, hashed249, hashed250, hashed251, hashed252, hashed253, hashed254, hashed255)
	"#)
}

#[cfg(test)]
mod tests {

	use super::*;

	#[test]
	fn create_with_no_alias() {
		assert_eq!(Import::new("./foo/bar/baz.code".to_string()), Import {
			source: String::from("./foo/bar/baz.code"),
			alias: None,
		});
	}

	#[test]
	fn create_with_alias() {
		assert_eq!(Import::new_with_alias("./foo/bar/baz.code".to_string(), &"myalias".to_string()), Import {
			source: String::from("./foo/bar/baz.code"),
			alias: Some("myalias".to_string()),
		});
	}
}
