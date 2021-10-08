extern crate proc_macro;

use quote::quote;
use syn::*;

#[proc_macro_attribute]
pub fn stopwatch(
    _attr: proc_macro::TokenStream,
    item: proc_macro::TokenStream,
) -> proc_macro::TokenStream {
    #[cfg(not(target_arch = "wasm32"))]
    {
        if let Ok(mut fun) = syn::parse::<ItemFn>(item.clone()) {
            let stmts = rewrite_function(fun.sig.ident.to_string(), &fun.block.stmts);
            fun.block.stmts = stmts;
            return quote!(#fun).into();
        }

        if let Ok(mut fun) = syn::parse::<TraitItemMethod>(item.clone()) {
            if let Some(block) = fun.default.as_mut() {
                let stmts = rewrite_function(fun.sig.ident.to_string(), &block.stmts);
                block.stmts = stmts;
                return quote!(#fun).into();
            }
        }

        if let Ok(mut fun) = syn::parse::<ImplItemMethod>(item) {
            let stmts = rewrite_function(fun.sig.ident.to_string(), &fun.block.stmts);
            fun.block.stmts = stmts;
            return quote!(#fun).into();
        }

        panic!("`zokrates_macro::stopwatch` should be used on functions")
    }

    #[cfg(target_arch = "wasm32")]
    item
}

fn rewrite_function(name: String, statements: &Vec<Stmt>) -> Vec<Stmt> {
    let block: Block = parse_quote! {{
        pub struct Stopwatch(std::time::Instant);

        impl Drop for Stopwatch {
            fn drop(&mut self) {
                log::debug!("Stopwatch: function `{}` was running for {}ms", #name, self.0.elapsed().as_millis());
            }
        }

        let _stopwatch = Stopwatch(std::time::Instant::now());
    }};

    let mut block_stmts = block.stmts;
    block_stmts.extend(statements.iter().cloned());
    block_stmts
}
