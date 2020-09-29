use core::convert::TryFrom;

use crate::constants::*;

#[derive(Debug)]
pub enum CurveDimension {
    Bn128,
    Bls12_381,
    Bls12_377,
    Bw6_761,
}

pub enum BackendDimension {
    Bellman,
    Zexe,
    #[cfg(feature = "libsnark")]
    Libsnark,
}

pub enum SchemeDimension {
    G16,
    GM17,
    #[cfg(feature = "libsnark")]
    PGHR13,
}

impl TryFrom<&str> for CurveDimension {
    type Error = String;

    fn try_from(s: &str) -> Result<Self, Self::Error> {
        match s {
            BN128 => Ok(CurveDimension::Bn128),
            BLS12_381 => Ok(CurveDimension::Bls12_381),
            BLS12_377 => Ok(CurveDimension::Bls12_377),
            BW6_761 => Ok(CurveDimension::Bw6_761),
            _ => Err(format!("Unknown curve {}", s)),
        }
    }
}

impl TryFrom<&str> for BackendDimension {
    type Error = String;

    fn try_from(s: &str) -> Result<Self, Self::Error> {
        match s {
            BELLMAN => Ok(BackendDimension::Bellman),
            ZEXE => Ok(BackendDimension::Zexe),
            #[cfg(feature = "libsnark")]
            LIBSNARK => Ok(BackendDimension::Libsnark),
            _ => Err(format!("Unknown backend {}", s)),
        }
    }
}

impl TryFrom<&str> for SchemeDimension {
    type Error = String;

    fn try_from(s: &str) -> Result<Self, Self::Error> {
        match s {
            G16 => Ok(SchemeDimension::G16),
            GM17 => Ok(SchemeDimension::GM17),
            #[cfg(feature = "libsnark")]
            PGHR13 => Ok(SchemeDimension::PGHR13),
            _ => Err(format!("Unknown proving scheme {}", s)),
        }
    }
}

pub struct Dimensions(
    pub BackendDimension,
    pub CurveDimension,
    pub SchemeDimension,
);

impl TryFrom<(&str, &str, &str)> for Dimensions {
    type Error = String;

    fn try_from(s: (&str, &str, &str)) -> Result<Dimensions, Self::Error> {
        let backend = BackendDimension::try_from(s.0)?;
        let curve = CurveDimension::try_from(s.1)?;
        let proving_scheme = SchemeDimension::try_from(s.2)?;

        match (&backend, &curve, &proving_scheme) {
            (BackendDimension::Bellman, CurveDimension::Bn128, SchemeDimension::G16) => {
                Ok(Dimensions(backend, curve, proving_scheme))
            }
            (BackendDimension::Bellman, CurveDimension::Bls12_381, SchemeDimension::G16) => {
                Ok(Dimensions(backend, curve, proving_scheme))
            }
            (BackendDimension::Zexe, CurveDimension::Bls12_377, SchemeDimension::GM17) => {
                Ok(Dimensions(backend, curve, proving_scheme))
            }
            (BackendDimension::Zexe, CurveDimension::Bw6_761, SchemeDimension::GM17) => {
                Ok(Dimensions(backend, curve, proving_scheme))
            }
            (BackendDimension::Zexe, CurveDimension::Bn128, SchemeDimension::GM17) => {
                Ok(Dimensions(backend, curve, proving_scheme))
            }
            #[cfg(feature = "libsnark")]
            (BackendDimension::Libsnark, CurveDimension::Bn128, SchemeDimension::GM17) => {
                Ok(Dimensions(backend, curve, proving_scheme))
            }
            #[cfg(feature = "libsnark")]
            (BackendDimension::Libsnark, CurveDimension::Bn128, SchemeDimension::PGHR13) => {
                Ok(Dimensions(backend, curve, proving_scheme))
            }
            _ => Err(format!(
                "Unsupported combination of dimensions (backend: {}, curve: {}, proving scheme: {})",
                s.0, s.1, s.2
            )),
        }
    }
}
