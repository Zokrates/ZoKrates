use crate::typed_absy::TypedModule;
use crate::typed_absy::{TypedFunctionSymbol, TypedProgram};
use zokrates_field::Field;

pub struct Trimmer;

impl Trimmer {
    pub fn trim<'ast, T: Field>(p: TypedProgram<'ast, T>) -> TypedProgram<'ast, T> {
        let main_module_id = p.main;

        // get the main module
        let main_module = p.modules.get(&main_module_id).unwrap().clone();

        // get the main function in the main module
        let (main_key, main_function) = main_module
            .functions
            .into_iter()
            .find(|(k, _)| k.id == "main")
            .unwrap()
            .clone();

        // define a function in the main module for the `unpack` embed
        let unpack = crate::embed::FlatEmbed::Unpack(T::get_required_bits());
        let unpack_key = unpack.key::<T>();

        // define a function in the main module for the `u32_to_bits` embed
        let u32_to_bits = crate::embed::FlatEmbed::U32ToBits;
        let u32_to_bits_key = u32_to_bits.key::<T>();

        // define a function in the main module for the `u16_to_bits` embed
        let u16_to_bits = crate::embed::FlatEmbed::U16ToBits;
        let u16_to_bits_key = u16_to_bits.key::<T>();

        // define a function in the main module for the `u8_to_bits` embed
        let u8_to_bits = crate::embed::FlatEmbed::U8ToBits;
        let u8_to_bits_key = u8_to_bits.key::<T>();

        // define a function in the main module for the `u32_from_bits` embed
        let u32_from_bits = crate::embed::FlatEmbed::U32FromBits;
        let u32_from_bits_key = u32_from_bits.key::<T>();

        // define a function in the main module for the `u16_from_bits` embed
        let u16_from_bits = crate::embed::FlatEmbed::U16FromBits;
        let u16_from_bits_key = u16_from_bits.key::<T>();

        // define a function in the main module for the `u8_from_bits` embed
        let u8_from_bits = crate::embed::FlatEmbed::U8FromBits;
        let u8_from_bits_key = u8_from_bits.key::<T>();

        TypedProgram {
            main: main_module_id.clone(),
            modules: vec![(
                main_module_id,
                TypedModule {
                    functions: vec![
                        (main_key, main_function),
                        (unpack_key.into(), TypedFunctionSymbol::Flat(unpack)),
                        (
                            u32_from_bits_key.into(),
                            TypedFunctionSymbol::Flat(u32_from_bits),
                        ),
                        (
                            u16_from_bits_key.into(),
                            TypedFunctionSymbol::Flat(u16_from_bits),
                        ),
                        (
                            u8_from_bits_key.into(),
                            TypedFunctionSymbol::Flat(u8_from_bits),
                        ),
                        (
                            u32_to_bits_key.into(),
                            TypedFunctionSymbol::Flat(u32_to_bits),
                        ),
                        (
                            u16_to_bits_key.into(),
                            TypedFunctionSymbol::Flat(u16_to_bits),
                        ),
                        (u8_to_bits_key.into(), TypedFunctionSymbol::Flat(u8_to_bits)),
                    ]
                    .into_iter()
                    .collect(),
                },
            )]
            .into_iter()
            .collect(),
        }
    }
}
