use ark_bw6_761::BW6_761;

use crate::G2Type;

prime_field!("bw6_761", BW6_761, G2Type::Fq);

ark_extensions!(BW6_761);
