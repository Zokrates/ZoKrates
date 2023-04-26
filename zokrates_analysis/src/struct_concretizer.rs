// After all generics are inlined, a program should be completely "concrete", which means that all types must only contain
// literals for array sizes. This is especially important to generate the ABI of the program.
// It is direct to ensure that with most types, however the way structs are implemented requires a slightly different process:
// Where for an array, `field[N]` ends up being propagated to `field[42]` which is direct to turn into a concrete type,
// for structs, `Foo<N> { field[N] a }` is propagated to `Foo<42> { field[N] a }`. The missing step is replacing `N` by `42`
// *inside* the canonical type, so that it can be concretized in the same way arrays are.

use std::marker::PhantomData;
use zokrates_ast::typed::folder::*;
use zokrates_ast::typed::{
    types::{
        ConcreteGenericsAssignment, DeclarationArrayType, DeclarationConstant,
        DeclarationStructMember, GGenericsAssignment,
    },
    DeclarationStructType, GenericIdentifier, TypedProgram,
};
use zokrates_field::Field;

pub struct StructConcretizer<'ast, T> {
    generics: ConcreteGenericsAssignment<'ast>,
    marker: PhantomData<T>,
}

impl<'ast, T: Field> StructConcretizer<'ast, T> {
    pub fn concretize(p: TypedProgram<'ast, T>) -> TypedProgram<'ast, T> {
        StructConcretizer::with_generics(ConcreteGenericsAssignment::default()).fold_program(p)
    }

    pub fn with_generics(generics: ConcreteGenericsAssignment<'ast>) -> Self {
        Self {
            generics,
            marker: PhantomData,
        }
    }
}

impl<'ast, T: Field> Folder<'ast, T> for StructConcretizer<'ast, T> {
    fn fold_declaration_struct_type(
        &mut self,
        ty: DeclarationStructType<'ast, T>,
    ) -> DeclarationStructType<'ast, T> {
        let concrete_generics: Vec<u32> = ty
            .generics
            .clone()
            .into_iter()
            .map(|g| g.unwrap().map_concrete(&self.generics).unwrap())
            .collect();

        let concrete_generics_map: ConcreteGenericsAssignment = GGenericsAssignment(
            concrete_generics
                .iter()
                .enumerate()
                .map(|(index, g)| (GenericIdentifier::without_name().with_index(index), *g))
                .collect(),
        );

        let mut internal_concretizer: StructConcretizer<'ast, T> =
            StructConcretizer::with_generics(concrete_generics_map);

        DeclarationStructType {
            members: ty
                .members
                .into_iter()
                .map(|member| {
                    DeclarationStructMember::new(
                        member.id,
                        internal_concretizer.fold_declaration_type(*member.ty),
                    )
                })
                .collect(),
            generics: concrete_generics
                .into_iter()
                .map(|g| Some(DeclarationConstant::Concrete(g)))
                .collect(),
            ..ty
        }
    }

    fn fold_declaration_array_type(
        &mut self,
        ty: DeclarationArrayType<'ast, T>,
    ) -> DeclarationArrayType<'ast, T> {
        let size = ty.size.map_concrete(&self.generics).unwrap();

        DeclarationArrayType::new(
            self.fold_declaration_type(*ty.ty),
            DeclarationConstant::Concrete(size),
        )
    }
}
