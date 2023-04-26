use crate::constants::*;
use std::convert::TryFrom;

#[derive(Debug, PartialEq, Eq)]
pub enum CurveParameter {
    Bn128,
    Bls12_381,
    Bls12_377,
    Bw6_761,
    Pallas,
    Vesta,
}

impl std::fmt::Display for CurveParameter {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use CurveParameter::*;

        match self {
            Bn128 => write!(f, "bn128"),
            Bls12_381 => write!(f, "bls12_381"),
            Bls12_377 => write!(f, "bls12_377"),
            Bw6_761 => write!(f, "bw6_761"),
            Pallas => write!(f, "pallas"),
            Vesta => write!(f, "vesta"),
        }
    }
}

#[derive(Debug, PartialEq, Eq)]
pub enum BackendParameter {
    #[cfg(feature = "bellman")]
    Bellman,
    #[cfg(feature = "ark")]
    Ark,
    #[cfg(feature = "bellperson")]
    Bellperson,
}

impl std::fmt::Display for BackendParameter {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use BackendParameter::*;

        match self {
            #[cfg(feature = "bellman")]
            Bellman => write!(f, "bellman"),
            #[cfg(feature = "ark")]
            Ark => write!(f, "ark"),
            #[cfg(feature = "bellperson")]
            Bellperson => write!(f, "bellperson"),
        }
    }
}

#[allow(clippy::upper_case_acronyms)]
#[derive(Debug, PartialEq, Eq)]
pub enum SchemeParameter {
    G16,
    GM17,
    MARLIN,
    NOVA,
}

impl std::fmt::Display for SchemeParameter {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use SchemeParameter::*;

        match self {
            G16 => write!(f, "g16"),
            GM17 => write!(f, "gm17"),
            MARLIN => write!(f, "marlin"),
            NOVA => write!(f, "nova"),
        }
    }
}

impl TryFrom<&str> for CurveParameter {
    type Error = String;

    fn try_from(s: &str) -> Result<Self, Self::Error> {
        match s {
            BN128 => Ok(CurveParameter::Bn128),
            BLS12_381 => Ok(CurveParameter::Bls12_381),
            BLS12_377 => Ok(CurveParameter::Bls12_377),
            BW6_761 => Ok(CurveParameter::Bw6_761),
            PALLAS => Ok(CurveParameter::Pallas),
            VESTA => Ok(CurveParameter::Vesta),
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
            #[cfg(feature = "bellperson")]
            BELLPERSON => Ok(BackendParameter::Bellperson),
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
            MARLIN => Ok(SchemeParameter::MARLIN),
            NOVA => Ok(SchemeParameter::NOVA),
            _ => Err(format!("Unknown proving scheme {}", s)),
        }
    }
}

#[derive(Debug)]
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
            (BackendParameter::Ark, CurveParameter::Bn128, SchemeParameter::G16) => Ok(()),
            #[cfg(feature = "ark")]
            (BackendParameter::Ark, CurveParameter::Bls12_381, SchemeParameter::G16) => Ok(()),
            #[cfg(feature = "ark")]
            (BackendParameter::Ark, CurveParameter::Bls12_377, SchemeParameter::G16) => Ok(()),
            #[cfg(feature = "ark")]
            (BackendParameter::Ark, CurveParameter::Bw6_761, SchemeParameter::G16) => Ok(()),
            #[cfg(feature = "ark")]
            (BackendParameter::Ark, CurveParameter::Bn128, SchemeParameter::GM17) => Ok(()),
            #[cfg(feature = "ark")]
            (BackendParameter::Ark, CurveParameter::Bls12_377, SchemeParameter::GM17) => Ok(()),
            #[cfg(feature = "ark")]
            (BackendParameter::Ark, CurveParameter::Bls12_381, SchemeParameter::GM17) => Ok(()),
            #[cfg(feature = "ark")]
            (BackendParameter::Ark, CurveParameter::Bw6_761, SchemeParameter::GM17) => Ok(()),
            #[cfg(feature = "ark")]
            (BackendParameter::Ark, CurveParameter::Bn128, SchemeParameter::MARLIN) => Ok(()),
            #[cfg(feature = "ark")]
            (BackendParameter::Ark, CurveParameter::Bls12_381, SchemeParameter::MARLIN) => Ok(()),
            #[cfg(feature = "ark")]
            (BackendParameter::Ark, CurveParameter::Bls12_377, SchemeParameter::MARLIN) => Ok(()),
            #[cfg(feature = "ark")]
            (BackendParameter::Ark, CurveParameter::Bw6_761, SchemeParameter::MARLIN) => Ok(()),
            #[cfg(feature = "bellperson")]
            (BackendParameter::Bellperson, CurveParameter::Pallas, SchemeParameter::NOVA) => Ok(()),
            #[cfg(feature = "bellperson")]
            (BackendParameter::Bellperson, CurveParameter::Vesta, SchemeParameter::NOVA) => Ok(()),
            #[cfg(feature = "bellman")]
            _ => Err(format!(
                "Unsupported combination of parameters (backend: {}, curve: {}, proving scheme: {})",
                s.0, s.1, s.2
            )),
        }.map(|_: ()| Parameters(backend, curve, proving_scheme))
    }
}
