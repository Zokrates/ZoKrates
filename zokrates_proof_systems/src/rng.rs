use blake2::{Blake2b, Digest};
use byteorder::ReadBytesExt;
use rand_0_8::{rngs::StdRng, SeedableRng};

pub fn get_rng_from_entropy(entropy: &str) -> StdRng {
    let h = {
        let mut h = Blake2b::default();
        h.input(entropy.as_bytes());
        h.result()
    };

    let mut digest = &h[..];
    let mut seed = [0u8; 32];

    for e in &mut seed {
        *e = digest.read_u8().unwrap();
    }

    StdRng::from_seed(seed)
}
