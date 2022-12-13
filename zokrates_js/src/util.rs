use rand_0_8::rngs::StdRng;
use rand_0_8::SeedableRng;
use std::path::{Component, PathBuf};

pub fn normalize_path(path: PathBuf) -> PathBuf {
    let mut components = path.components().peekable();
    let mut ret = if let Some(c @ Component::Prefix(..)) = components.peek().cloned() {
        components.next();
        PathBuf::from(c.as_os_str())
    } else {
        PathBuf::new()
    };

    for component in components {
        match component {
            Component::Prefix(..) => unreachable!(),
            Component::RootDir => {
                ret.push(component.as_os_str());
            }
            Component::CurDir => {}
            Component::ParentDir => {
                ret.pop();
            }
            Component::Normal(c) => {
                ret.push(c);
            }
        }
    }
    ret
}

pub fn get_seeded_rng(entropy: &str) -> StdRng {
    use blake2::{Blake2b, Digest};
    use byteorder::ReadBytesExt;

    let h = {
        let mut h = Blake2b::default();
        h.input(&entropy.as_bytes());
        h.result()
    };

    let mut digest = &h[..];
    let mut seed = [0u8; 32];

    for e in &mut seed {
        *e = digest.read_u8().unwrap();
    }

    StdRng::from_seed(seed)
}
