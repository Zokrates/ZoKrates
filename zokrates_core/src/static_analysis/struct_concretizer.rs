// After all generics are inlined, a program should be completely "concrete", which means that all types must only contain
// litterals for array sizes. This is especially important to generate the ABI of the program.
// It is direct to ensure that with most types, however the way structs are implemented requires a slightly different process:
// Where for an array, `field[N]` ends up being propagated to `field[42]` which is direct to turn into a concrete type,
// for structs, `Foo<N> { field[N] a }` is propagated to `Foo<42> { field[N] a }`. The missing step is replacing `N` by `42`
// *inside* the canonical type, so that it can be concretized in the same way arrays are.
// We apply this transformation only to the main function.

use crate::typed_absy::folder::*;
use crate::typed_absy::{
    types::{
        ConcreteGenericsAssignment, DeclarationArrayType, DeclarationConstant,
        DeclarationStructMember, GGenericsAssignment,
    },
    DeclarationStructType, GenericIdentifier, TypedProgram,
};
use zokrates_field::Field;

#[derive(Default)]
pub struct StructConcretizer<'ast> {
    generics: ConcreteGenericsAssignment<'ast>,
}

impl<'ast> StructConcretizer<'ast> {
    pub fn concretize<T: Field>(p: TypedProgram<'ast, T>) -> TypedProgram<'ast, T> {
        StructConcretizer::default().fold_program(p)
    }

    pub fn with_generics(generics: ConcreteGenericsAssignment<'ast>) -> Self {
        Self { generics }
    }
}

impl<'ast, T: Field> Folder<'ast, T> for StructConcretizer<'ast> {
    fn fold_declaration_struct_type(
        &mut self,
        ty: DeclarationStructType<'ast>,
    ) -> DeclarationStructType<'ast> {
        let concrete_generics: Vec<_> = ty
            .generics
            .iter()
            .map(|g| match g.as_ref().unwrap() {
                DeclarationConstant::Generic(s) => self.generics.0.get(&s).cloned().unwrap(),
                DeclarationConstant::Concrete(s) => *s as usize,
                DeclarationConstant::Constant(..) => unreachable!(),
            })
            .collect();

        let concrete_generics_map: ConcreteGenericsAssignment = GGenericsAssignment(
            concrete_generics
                .iter()
                .enumerate()
                .map(|(index, g)| (GenericIdentifier::with_name("DUMMY").index(index), *g))
                .collect(),
        );

        let mut internal_concretizer = StructConcretizer::with_generics(concrete_generics_map);

        DeclarationStructType {
            members: ty
                .members
                .into_iter()
                .map(|member| {
                    DeclarationStructMember::new(
                        member.id,
                        <StructConcretizer as Folder<'ast, T>>::fold_declaration_type(
                            &mut internal_concretizer,
                            *member.ty,
                        ),
                    )
                })
                .collect(),
            generics: concrete_generics
                .into_iter()
                .map(|g| Some(DeclarationConstant::Concrete(g as u32)))
                .collect(),
            ..ty
        }
    }

    fn fold_declaration_array_type(
        &mut self,
        ty: DeclarationArrayType<'ast>,
    ) -> DeclarationArrayType<'ast> {
        let size = match ty.size {
            DeclarationConstant::Generic(s) => self.generics.0.get(&s).cloned().unwrap() as u32,
            DeclarationConstant::Concrete(s) => s,
            DeclarationConstant::Constant(..) => unreachable!(),
        };

        DeclarationArrayType {
            size: DeclarationConstant::Concrete(size),
            ty: box <StructConcretizer as Folder<'ast, T>>::fold_declaration_type(self, *ty.ty),
        }
    }
}
