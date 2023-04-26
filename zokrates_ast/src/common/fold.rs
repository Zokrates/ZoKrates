pub trait Fold<F>: Sized {
    fn fold(self, f: &mut F) -> Self;
}

pub trait ResultFold<F, E>: Sized {
    fn fold(self, f: &mut F) -> Result<Self, E>;
}
