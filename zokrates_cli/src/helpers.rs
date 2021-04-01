use crate::constants::*;
use std::convert::TryFrom;

#[derive(Debug)]
pub enum CurveParameter {
    Bn128,
    Bls12_381,
    Bls12_377,
    Bw6_761,
}

pub enum BackendParameter {
    #[cfg(feature = "bellman")]
    Bellman,
    #[cfg(feature = "ark")]
    Ark,
    #[cfg(feature = "libsnark")]
    Libsnark,
}

#[allow(clippy::upper_case_acronyms)]
pub enum SchemeParameter {
    G16,
    GM17,
    PGHR13,
}

impl TryFrom<&str> for CurveParameter {
    type Error = String;

    fn try_from(s: &str) -> Result<Self, Self::Error> {
        match s {
            BN128 => Ok(CurveParameter::Bn128),
            BLS12_381 => Ok(CurveParameter::Bls12_381),
            BLS12_377 => Ok(CurveParameter::Bls12_377),
            BW6_761 => Ok(CurveParameter::Bw6_761),
            _ => Err(format!("Unknown curve {}", s)),
        }
    }
}

impl TryFrom<&str> for BackendParameter {
    type Error = String;

    fn try_from(s: &str) -> Result<Self, Self::Error> {
        match s {
            #[cfg(feature = "bellman")]
            BELLMAN => Ok(BackendParameter::Bellman),
            #[cfg(feature = "ark")]
            ARK => Ok(BackendParameter::Ark),
            #[cfg(feature = "libsnark")]
            LIBSNARK => Ok(BackendParameter::Libsnark),
            _ => Err(format!("Unknown backend {}", s)),
        }
    }
}

impl TryFrom<&str> for SchemeParameter {
    type Error = String;

    fn try_from(s: &str) -> Result<Self, Self::Error> {
        match s {
            G16 => Ok(SchemeParameter::G16),
            GM17 => Ok(SchemeParameter::GM17),
            PGHR13 => Ok(SchemeParameter::PGHR13),
            _ => Err(format!("Unknown proving scheme {}", s)),
        }
    }
}

pub struct Parameters(
    pub BackendParameter,
    pub CurveParameter,
    pub SchemeParameter,
);

impl TryFrom<(&str, &str, &str)> for Parameters {
    type Error = String;

    fn try_from(s: (&str, &str, &str)) -> Result<Parameters, Self::Error> {
        let backend = BackendParameter::try_from(s.0)?;
        let curve = CurveParameter::try_from(s.1)?;
        let proving_scheme = SchemeParameter::try_from(s.2)?;

        match (&backend, &curve, &proving_scheme) {
            #[cfg(feature = "bellman")]
            (BackendParameter::Bellman, CurveParameter::Bn128, SchemeParameter::G16) => Ok(()),
            #[cfg(feature = "bellman")]
            (BackendParameter::Bellman, CurveParameter::Bls12_381, SchemeParameter::G16) => Ok(()),
            #[cfg(feature = "ark")]
            (BackendParameter::Ark, CurveParameter::Bls12_377, SchemeParameter::GM17) => Ok(()),
            #[cfg(feature = "ark")]
            (BackendParameter::Ark, CurveParameter::Bw6_761, SchemeParameter::GM17) => Ok(()),
            #[cfg(feature = "ark")]
            (BackendParameter::Ark, CurveParameter::Bn128, SchemeParameter::GM17) => Ok(()),
            #[cfg(feature = "libsnark")]
            (BackendParameter::Libsnark, CurveParameter::Bn128, SchemeParameter::GM17) => Ok(()),
            #[cfg(feature = "libsnark")]
            (BackendParameter::Libsnark, CurveParameter::Bn128, SchemeParameter::PGHR13) => Ok(()),
            _ => Err(format!(
                "Unsupported combination of parameters (backend: {}, curve: {}, proving scheme: {})",
                s.0, s.1, s.2
            )),
        }.map(|_: ()| Parameters(backend, curve, proving_scheme))
    }
}
