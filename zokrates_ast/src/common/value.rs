pub trait Value {
    type Value: Clone;

    fn as_value(&self) -> Option<&Self::Value> {
        unimplemented!()
    }
}
