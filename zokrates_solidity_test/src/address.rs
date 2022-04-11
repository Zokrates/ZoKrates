use ethabi::token::Token;
use primitive_types::H160;
use rand::Rng;

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Address(pub H160);

impl Address {
    pub fn random<R: Rng>(rng: &mut R) -> Self {
        Self(H160(rng.gen()))
    }

    pub fn as_token(&self) -> Token {
        Token::Address(self.0)
    }
}

impl AsRef<H160> for Address {
    fn as_ref(&self) -> &H160 {
        &self.0
    }
}

impl From<H160> for Address {
    fn from(hash: H160) -> Self {
        Self(hash)
    }
}
