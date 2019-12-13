use typed_absy;
use zir;

impl<'ast> From<typed_absy::types::FunctionKey<'ast>> for zir::types::FunctionKey<'ast> {
fn from(
    k: typed_absy::types::FunctionKey<'ast>,
) -> zir::types::FunctionKey<'ast> {
    zir::types::FunctionKey {
        id: k.id,
        signature: k.signature.into()
    }
}
}
impl From<typed_absy::types::Signature> for zir::types::Signature {
fn from(
    s: typed_absy::types::Signature,
) -> zir::types::Signature {
    zir::types::Signature {
        inputs: s.inputs.into_iter().flat_map(|t| from_type(t)).collect(),
        outputs: s.outputs.into_iter().flat_map(|t| from_type(t)).collect(),
    }
}
}

fn from_type(
    t: typed_absy::types::Type,
) -> Vec<zir::types::Type> {
    match t {
        typed_absy::Type::FieldElement => vec![zir::Type::FieldElement,
        ],
        typed_absy::Type::Boolean => vec![zir::Type::Boolean,
        ],
        typed_absy::Type::Uint(bitwidth) => vec![zir::Type::Uint(bitwidth),
        ],
        typed_absy::Type::Array(array_type) => {
            let inner = from_type(*array_type.ty);
            (0..array_type.size)
            .flat_map(|i| inner.clone())
            .collect()
        },
        typed_absy::Type::Struct(members) => members
            .into_iter()
            .flat_map(|struct_member| 
                from_type(*struct_member.ty)
            )
            .collect(),
    }
}