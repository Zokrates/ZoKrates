// A folder to inline all constant definitions down to a single literal and register them in the state for later use.

use crate::reducer::{
    constants_reader::ConstantsReader, reduce_function, ConstantDefinitions, Error,
};
use std::collections::HashSet;
use zokrates_ast::typed::{
    result_folder::*, Constant, ModuleId, OwnedModuleId, Typed, TypedConstant, TypedConstantSymbol,
    TypedConstantSymbolDeclaration, TypedProgram, TypedSymbolDeclaration, UExpression,
};
use zokrates_field::Field;

pub struct ConstantsWriter<'ast, T> {
    treated: HashSet<OwnedModuleId>,
    constants: ConstantDefinitions<'ast, T>,
    location: OwnedModuleId,
    program: TypedProgram<'ast, T>,
}

impl<'ast, T: Field> ConstantsWriter<'ast, T> {
    pub fn with_program(program: TypedProgram<'ast, T>) -> Self {
        ConstantsWriter {
            constants: ConstantDefinitions::default(),
            location: program.main.clone(),
            treated: HashSet::default(),
            program,
        }
    }

    fn change_location(&mut self, location: OwnedModuleId) -> OwnedModuleId {
        let prev = self.location.clone();
        self.location = location;
        self.treated.insert(self.location.clone());
        prev
    }

    fn treated(&self, id: &ModuleId) -> bool {
        self.treated.contains(id)
    }

    fn update_program(&mut self) {
        let mut p = TypedProgram::default();
        std::mem::swap(&mut self.program, &mut p);
        self.program = ConstantsReader::with_constants(&self.constants).read_into_program(p);
    }

    fn update_symbol_declaration(
        &self,
        d: TypedSymbolDeclaration<'ast, T>,
    ) -> TypedSymbolDeclaration<'ast, T> {
        ConstantsReader::with_constants(&self.constants).read_into_symbol_declaration(d)
    }
}

impl<'ast, T: Field> ResultFolder<'ast, T> for ConstantsWriter<'ast, T> {
    type Error = Error;

    fn fold_module_id(&mut self, id: OwnedModuleId) -> Result<OwnedModuleId, Self::Error> {
        // anytime we encounter a module id, visit the corresponding module if it hasn't been done yet
        if !self.treated(&id) {
            let current_m_id = self.change_location(id.clone());
            // I did not find a way to achieve this without cloning the module. Assuming we do not clone:
            // to fold the module, we need to consume it, so it gets removed from the modules
            // but to inline the calls while folding the module, all modules must be present
            // therefore we clone...
            // this does not lead to a module being folded more than once, as the first time
            // we change location to this module, it's added to the `treated` set
            let m = self.program.modules.get(&id).cloned().unwrap();
            let m = self.fold_module(m)?;
            self.program.modules.insert(id.clone(), m);
            self.change_location(current_m_id);
        }
        Ok(id)
    }

    fn fold_symbol_declaration(
        &mut self,
        s: TypedSymbolDeclaration<'ast, T>,
    ) -> Result<TypedSymbolDeclaration<'ast, T>, Self::Error> {
        // before we treat the symbol, propagate the constants into it, as it may be using constants defined earlier in this module.
        let s = self.update_symbol_declaration(s);

        let s = fold_symbol_declaration(self, s)?;

        // after we treat the symbol, propagate again, as treating this symbol may have triggered checking another module, resolving new constants which this symbol may be using.
        Ok(self.update_symbol_declaration(s))
    }

    fn fold_constant_symbol_declaration(
        &mut self,
        d: TypedConstantSymbolDeclaration<'ast, T>,
    ) -> Result<TypedConstantSymbolDeclaration<'ast, T>, Self::Error> {
        let id = self.fold_canonical_constant_identifier(d.id)?;

        match d.symbol {
            TypedConstantSymbol::Here(c) => {
                let c = self.fold_constant(c)?;

                // if constants were used in the rhs, they are now defined in the map
                // replace them in the expression
                use zokrates_ast::typed::folder::Folder;

                let c = ConstantsReader::with_constants(&self.constants).fold_constant(c);

                use zokrates_ast::typed::{DeclarationSignature, TypedFunction, TypedStatement};

                // wrap this expression in a function
                let wrapper = TypedFunction {
                    arguments: vec![],
                    statements: vec![TypedStatement::ret(c.expression)],
                    signature: DeclarationSignature::new().output(c.ty.clone()),
                };

                let mut inlined_wrapper = reduce_function(wrapper, &self.program)?;

                if let TypedStatement::Return(ret) = inlined_wrapper.statements.pop().unwrap() {
                    let expression = ret.inner;

                    if !expression.is_constant() {
                        return Err(Error::ConstantReduction(id.id.to_string(), id.module));
                    };

                    if zokrates_ast::typed::types::try_from_g_type::<_, UExpression<'ast, T>>(
                        c.ty.clone(),
                    )
                    .unwrap()
                        == expression.get_type()
                    {
                        // add to the constant map
                        self.constants.insert(id.clone(), expression.clone());

                        // after we reduced a constant, propagate it through the whole program
                        self.update_program();

                        Ok(TypedConstantSymbolDeclaration {
                            id,
                            symbol: TypedConstantSymbol::Here(TypedConstant {
                                expression,
                                ty: c.ty,
                            }),
                        })
                    } else {
                        Err(Error::Type(format!("Expression of type `{}` cannot be assigned to constant `{}` of type `{}`", expression.get_type(), id, c.ty)))
                    }
                } else {
                    Err(Error::ConstantReduction(id.id.to_string(), id.module))
                }
            }
            _ => unreachable!("all constants should be local"),
        }
    }
}
