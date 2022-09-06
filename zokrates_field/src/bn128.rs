use ark_bn254::Bn254;

prime_field!("bn128", Bn254, G2Type::Fq2);

ark_extensions!(Bn254);

#[cfg(feature = "bellman")]
use bellman_ce::pairing::bn256::{Bn256, Fq2};

use crate::G2Type;
#[cfg(feature = "bellman")]
bellman_extensions!(Bn256, Fq2);

#[cfg(test)]
mod tests {
    use super::*;

    impl<'a> From<&'a str> for FieldPrime {
        fn from(s: &'a str) -> FieldPrime {
            FieldPrime::try_from_dec_str(s).unwrap()
        }
    }

    #[cfg(test)]
    mod field_prime {
        use super::*;
        use bincode::{deserialize, serialize, Infinite};

        #[test]
        fn to_bits_be() {
            let bits = FieldPrime::max_value().to_bits_be();
            assert_eq!(bits.len(), 254);
            assert_eq!(
                bits[0..10].to_vec(),
                vec![true, true, false, false, false, false, false, true, true, false]
            );

            let bits = FieldPrime::one().to_bits_be();
            assert_eq!(bits.len(), 254);
            assert!(bits[253]);
        }

        #[test]
        fn addition() {
            assert_eq!(
                FieldPrime::from("65484493"),
                FieldPrime::from("65416358") + FieldPrime::from("68135")
            );
            assert_eq!(
                FieldPrime::from("65484493"),
                FieldPrime::from("65416358") + &FieldPrime::from("68135")
            );
        }

        #[test]
        fn addition_negative_small() {
            assert_eq!(
                FieldPrime::from("3"),
                FieldPrime::from("5") + FieldPrime::from(-2)
            );
            assert_eq!(
                FieldPrime::from("3"),
                FieldPrime::from("5") + &FieldPrime::from(-2)
            );
        }

        #[test]
        fn addition_negative() {
            assert_eq!(
                FieldPrime::from("65348223"),
                FieldPrime::from("65416358") + FieldPrime::from(-68135)
            );
            assert_eq!(
                FieldPrime::from("65348223"),
                FieldPrime::from("65416358") + &FieldPrime::from(-68135)
            );
        }

        #[test]
        fn subtraction() {
            assert_eq!(
                FieldPrime::from("65348223"),
                FieldPrime::from("65416358") - FieldPrime::from("68135")
            );
            assert_eq!(
                FieldPrime::from("65348223"),
                FieldPrime::from("65416358") - &FieldPrime::from("68135")
            );
        }

        #[test]
        fn subtraction_negative() {
            assert_eq!(
                FieldPrime::from("65484493"),
                FieldPrime::from("65416358") - FieldPrime::from(-68135)
            );
            assert_eq!(
                FieldPrime::from("65484493"),
                FieldPrime::from("65416358") - &FieldPrime::from(-68135)
            );
        }

        #[test]
        fn subtraction_overflow() {
            assert_eq!(
                FieldPrime::from(
                    "21888242871839275222246405745257275088548364400416034343698204186575743147394"
                ),
                FieldPrime::from("68135") - FieldPrime::from("65416358")
            );
            assert_eq!(
                FieldPrime::from(
                    "21888242871839275222246405745257275088548364400416034343698204186575743147394"
                ),
                FieldPrime::from("68135") - &FieldPrime::from("65416358")
            );
        }

        #[test]
        fn multiplication() {
            assert_eq!(
                FieldPrime::from("13472"),
                FieldPrime::from("32") * FieldPrime::from("421")
            );
            assert_eq!(
                FieldPrime::from("13472"),
                FieldPrime::from("32") * &FieldPrime::from("421")
            );
        }

        #[test]
        fn multiplication_negative() {
            assert_eq!(
                FieldPrime::from(
                    "21888242871839275222246405745257275088548364400416034343698204186575808014369"
                ),
                FieldPrime::from("54") * FieldPrime::from(-8912)
            );
            assert_eq!(
                FieldPrime::from(
                    "21888242871839275222246405745257275088548364400416034343698204186575808014369"
                ),
                FieldPrime::from("54") * &FieldPrime::from(-8912)
            );
        }

        #[test]
        fn multiplication_two_negative() {
            assert_eq!(
                FieldPrime::from("648"),
                FieldPrime::from(-54) * FieldPrime::from(-12)
            );
            assert_eq!(
                FieldPrime::from("648"),
                FieldPrime::from(-54) * &FieldPrime::from(-12)
            );
        }

        #[test]
        fn multiplication_overflow() {
            assert_eq!(
                FieldPrime::from(
                    "6042471409729479866150380306128222617399890671095126975526159292198160466142"
                ),
                FieldPrime::from(
                    "21888242871839225222246405785257275088694311157297823662689037894645225727"
                ) * FieldPrime::from("218882428715392752222464057432572755886923")
            );
            assert_eq!(
                FieldPrime::from(
                    "6042471409729479866150380306128222617399890671095126975526159292198160466142"
                ),
                FieldPrime::from(
                    "21888242871839225222246405785257275088694311157297823662689037894645225727"
                ) * &FieldPrime::from("218882428715392752222464057432572755886923")
            );
        }

        #[test]
        fn division() {
            assert_eq!(
                FieldPrime::from(4),
                FieldPrime::from(48) / FieldPrime::from(12)
            );
            assert_eq!(
                FieldPrime::from(4),
                FieldPrime::from(48) / &FieldPrime::from(12)
            );
        }

        #[test]
        fn required_bits() {
            assert_eq!(FieldPrime::get_required_bits(), 254);
        }

        #[test]
        fn bits() {
            assert_eq!(FieldPrime::from(0).bits(), 1);
            assert_eq!(FieldPrime::from(1).bits(), 1);
            assert_eq!(FieldPrime::from(2).bits(), 2);
            assert_eq!(FieldPrime::from(3).bits(), 2);
            assert_eq!(FieldPrime::from(4).bits(), 3);
        }

        #[test]
        fn to_biguint() {
            assert_eq!(
                FieldPrime::try_from(FieldPrime::from(2).to_biguint()),
                Ok(FieldPrime::from(2))
            );
            assert_eq!(
                FieldPrime::try_from(FieldPrime::from(0).to_biguint()),
                Ok(FieldPrime::from(0))
            );
            assert_eq!(
                FieldPrime::try_from(FieldPrime::max_value().to_biguint()),
                Ok(FieldPrime::max_value())
            );
        }

        #[test]
        fn division_negative() {
            let res = FieldPrime::from(-54) / FieldPrime::from(12);
            assert_eq!(FieldPrime::from(-54), FieldPrime::from(12) * res);
        }

        #[test]
        fn division_two_negative() {
            let res = FieldPrime::from(-12) / FieldPrime::from(-85);
            assert_eq!(FieldPrime::from(-12), FieldPrime::from(-85) * res);
        }

        #[test]
        fn pow_usize() {
            assert_eq!(
                FieldPrime::from("614787626176508399616"),
                FieldPrime::from("54").pow(12)
            );
        }

        #[test]
        fn serde_ser_deser() {
            let serialized = &serialize(&FieldPrime::from("11"), Infinite).unwrap();
            let deserialized = deserialize(serialized).unwrap();
            assert_eq!(FieldPrime::from("11"), deserialized);
        }

        #[test]
        fn serde_json_ser_deser() {
            let serialized = serde_json::to_string(&FieldPrime::from("11")).unwrap();
            let deserialized = serde_json::from_str(&serialized).unwrap();
            assert_eq!(FieldPrime::from("11"), deserialized);
        }

        #[test]
        fn bytes_ser_deser() {
            let fp = FieldPrime::from("101");
            let bv = fp.to_byte_vector();
            assert_eq!(fp, FieldPrime::from_byte_vector(bv));
        }

        #[test]
        fn dec_string_ser_deser() {
            let fp = FieldPrime::from("101");
            let bv = fp.to_dec_string();
            assert_eq!(fp, FieldPrime::try_from_dec_str(&bv).unwrap());
        }

        #[test]
        fn compact_representation() {
            let one = FieldPrime::from(1);
            assert_eq!("1", &one.to_compact_dec_string());
            let minus_one = FieldPrime::from(0) - one;
            assert_eq!("(-1)", &minus_one.to_compact_dec_string());
            // (p-1)/2 -> positive notation
            let p_minus_one_over_two =
                (FieldPrime::from(0) - FieldPrime::from(1)) / FieldPrime::from(2);
            assert_eq!(
                "10944121435919637611123202872628637544274182200208017171849102093287904247808",
                &p_minus_one_over_two.to_compact_dec_string()
            );
            // (p-1)/2 + 1 -> negative notation (p-1)/2 + 1 - p == (-p+1)/2
            let p_minus_one_over_two_plus_one = ((FieldPrime::from(0) - FieldPrime::from(1))
                / FieldPrime::from(2))
                + FieldPrime::from(1);
            assert_eq!(
                "(-10944121435919637611123202872628637544274182200208017171849102093287904247808)",
                &p_minus_one_over_two_plus_one.to_compact_dec_string()
            );
        }
    }

    #[cfg(feature = "bellman")]
    mod bellman {
        use super::*;

        use bellman_ce::pairing::ff::Field as FField;

        extern crate rand;
        use bellman_ce::pairing::bn256::Fr;

        use rand::{thread_rng, Rng};

        #[test]
        fn fr_to_field_to_fr() {
            let rng = &mut thread_rng();
            for _ in 0..1000 {
                let a: Fr = rng.gen();
                assert_eq!(FieldPrime::from_bellman(a).into_bellman(), a);
            }
        }

        #[test]
        fn field_to_fr_to_field() {
            // use Fr to get a random element
            let rng = &mut thread_rng();
            for _ in 0..1000 {
                let a: Fr = rng.gen();
                // now test idempotence
                let a = FieldPrime::from_bellman(a);
                assert_eq!(FieldPrime::from_bellman(a.clone().into_bellman()), a);
            }
        }

        #[test]
        fn one() {
            let a = FieldPrime::from(1);

            assert_eq!(a.into_bellman(), Fr::one());
        }

        #[test]
        fn zero() {
            let a = FieldPrime::from(0);

            assert_eq!(a.into_bellman(), Fr::zero());
        }

        #[test]
        fn minus_one() {
            let mut a: Fr = Fr::one();
            a.negate();
            assert_eq!(FieldPrime::from_bellman(a), FieldPrime::from(-1));
        }

        #[test]
        fn add() {
            let rng = &mut thread_rng();

            let mut a: Fr = rng.gen();
            let b: Fr = rng.gen();

            let aa = FieldPrime::from_bellman(a);
            let bb = FieldPrime::from_bellman(b);
            let cc = aa + bb;

            a.add_assign(&b);

            assert_eq!(FieldPrime::from_bellman(a), cc);
        }
    }
}
