prime_field!(
    b"21888242871839275222246405745257275088548364400416034343698204186575808495617",
    "bn128"
);

#[cfg(feature = "bellman")]
use bellman_ce::pairing::bn256::{Bn256, Fq2};
#[cfg(feature = "bellman")]
bellman_extensions!(Bn256, Fq2);

#[cfg(feature = "ark")]
use ark_bn254::Bn254;
#[cfg(feature = "ark")]
ark_extensions!(Bn254);

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
        fn max_value_bits() {
            let bits = FieldPrime::max_value_bit_vector_be();
            assert_eq!(
                bits[0..10].to_vec(),
                vec![true, true, false, false, false, false, false, true, true, false]
            );
        }

        #[test]
        fn positive_number() {
            assert_eq!(
                "1234245612".parse::<BigInt>().unwrap(),
                FieldPrime::from("1234245612").value
            );
        }

        #[test]
        fn negative_number() {
            assert_eq!(
                P.checked_sub(&"12".parse::<BigInt>().unwrap()).unwrap(),
                FieldPrime::from("-12").value
            );
        }

        #[test]
        fn addition() {
            assert_eq!(
                "65484493".parse::<BigInt>().unwrap(),
                (FieldPrime::from("65416358") + FieldPrime::from("68135")).value
            );
            assert_eq!(
                "65484493".parse::<BigInt>().unwrap(),
                (FieldPrime::from("65416358") + &FieldPrime::from("68135")).value
            );
        }

        #[test]
        fn addition_negative_small() {
            assert_eq!(
                "3".parse::<BigInt>().unwrap(),
                (FieldPrime::from("5") + FieldPrime::from("-2")).value
            );
            assert_eq!(
                "3".parse::<BigInt>().unwrap(),
                (FieldPrime::from("5") + &FieldPrime::from("-2")).value
            );
        }

        #[test]
        fn addition_negative() {
            assert_eq!(
                "65348223".parse::<BigInt>().unwrap(),
                (FieldPrime::from("65416358") + FieldPrime::from("-68135")).value
            );
            assert_eq!(
                "65348223".parse::<BigInt>().unwrap(),
                (FieldPrime::from("65416358") + &FieldPrime::from("-68135")).value
            );
        }

        #[test]
        fn subtraction() {
            assert_eq!(
                "65348223".parse::<BigInt>().unwrap(),
                (FieldPrime::from("65416358") - FieldPrime::from("68135")).value
            );
            assert_eq!(
                "65348223".parse::<BigInt>().unwrap(),
                (FieldPrime::from("65416358") - &FieldPrime::from("68135")).value
            );
        }

        #[test]
        fn subtraction_negative() {
            assert_eq!(
                "65484493".parse::<BigInt>().unwrap(),
                (FieldPrime::from("65416358") - FieldPrime::from("-68135")).value
            );
            assert_eq!(
                "65484493".parse::<BigInt>().unwrap(),
                (FieldPrime::from("65416358") - &FieldPrime::from("-68135")).value
            );
        }

        #[test]
        fn subtraction_overflow() {
            assert_eq!(
                "21888242871839275222246405745257275088548364400416034343698204186575743147394"
                    .parse::<BigInt>()
                    .unwrap(),
                (FieldPrime::from("68135") - FieldPrime::from("65416358")).value
            );
            assert_eq!(
                "21888242871839275222246405745257275088548364400416034343698204186575743147394"
                    .parse::<BigInt>()
                    .unwrap(),
                (FieldPrime::from("68135") - &FieldPrime::from("65416358")).value
            );
        }

        #[test]
        fn multiplication() {
            assert_eq!(
                "13472".parse::<BigInt>().unwrap(),
                (FieldPrime::from("32") * FieldPrime::from("421")).value
            );
            assert_eq!(
                "13472".parse::<BigInt>().unwrap(),
                (FieldPrime::from("32") * &FieldPrime::from("421")).value
            );
        }

        #[test]
        fn multiplication_negative() {
            assert_eq!(
                "21888242871839275222246405745257275088548364400416034343698204186575808014369"
                    .parse::<BigInt>()
                    .unwrap(),
                (FieldPrime::from("54") * FieldPrime::from("-8912")).value
            );
            assert_eq!(
                "21888242871839275222246405745257275088548364400416034343698204186575808014369"
                    .parse::<BigInt>()
                    .unwrap(),
                (FieldPrime::from("54") * &FieldPrime::from("-8912")).value
            );
        }

        #[test]
        fn multiplication_two_negative() {
            assert_eq!(
                "648".parse::<BigInt>().unwrap(),
                (FieldPrime::from("-54") * FieldPrime::from("-12")).value
            );
            assert_eq!(
                "648".parse::<BigInt>().unwrap(),
                (FieldPrime::from("-54") * &FieldPrime::from("-12")).value
            );
        }

        #[test]
        fn multiplication_overflow() {
            assert_eq!(
                "6042471409729479866150380306128222617399890671095126975526159292198160466142"
                    .parse::<BigInt>()
                    .unwrap(),
                (FieldPrime::from(
                    "21888242871839225222246405785257275088694311157297823662689037894645225727"
                ) * FieldPrime::from("218882428715392752222464057432572755886923"))
                .value
            );
            assert_eq!(
                "6042471409729479866150380306128222617399890671095126975526159292198160466142"
                    .parse::<BigInt>()
                    .unwrap(),
                (FieldPrime::from(
                    "21888242871839225222246405785257275088694311157297823662689037894645225727"
                ) * &FieldPrime::from("218882428715392752222464057432572755886923"))
                    .value
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
                "614787626176508399616".parse::<BigInt>().unwrap(),
                (FieldPrime::from("54").pow(12)).value
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

    #[test]
    fn bigint_assertions() {
        let x = BigInt::parse_bytes(b"65", 10).unwrap();
        assert_eq!(&x + &x, BigInt::parse_bytes(b"130", 10).unwrap());
        assert_eq!(
            "1".parse::<BigInt>().unwrap(),
            "3".parse::<BigInt>()
                .unwrap()
                .div_floor(&"2".parse::<BigInt>().unwrap())
        );
        assert_eq!(
            "-2".parse::<BigInt>().unwrap(),
            "-3".parse::<BigInt>()
                .unwrap()
                .div_floor(&"2".parse::<BigInt>().unwrap())
        );
    }

    #[test]
    fn test_extended_euclid() {
        assert_eq!(
            (
                ToBigInt::to_bigint(&1).unwrap(),
                ToBigInt::to_bigint(&-9).unwrap(),
                ToBigInt::to_bigint(&47).unwrap()
            ),
            extended_euclid(
                &ToBigInt::to_bigint(&120).unwrap(),
                &ToBigInt::to_bigint(&23).unwrap()
            )
        );
        assert_eq!(
            (
                ToBigInt::to_bigint(&2).unwrap(),
                ToBigInt::to_bigint(&2).unwrap(),
                ToBigInt::to_bigint(&-11).unwrap()
            ),
            extended_euclid(
                &ToBigInt::to_bigint(&122).unwrap(),
                &ToBigInt::to_bigint(&22).unwrap()
            )
        );
        assert_eq!(
            (
                ToBigInt::to_bigint(&2).unwrap(),
                ToBigInt::to_bigint(&-9).unwrap(),
                ToBigInt::to_bigint(&47).unwrap()
            ),
            extended_euclid(
                &ToBigInt::to_bigint(&240).unwrap(),
                &ToBigInt::to_bigint(&46).unwrap()
            )
        );
        let (b, s, _) = extended_euclid(&ToBigInt::to_bigint(&253).unwrap(), &*P);
        assert_eq!(b, BigInt::one());
        let s_field = FieldPrime {
            value: &s - s.div_floor(&*P) * &*P,
        };
        assert_eq!(
            FieldPrime::from(
                "12717674712096337777352654721552646000065650461901806515903699665717959876900"
            ),
            s_field
        );
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
