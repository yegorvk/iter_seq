use typenum::{Const, Unsigned};

pub trait ToUInt: typenum::ToUInt {
    type Output: Unsigned;
}

impl<T: typenum::ToUInt> ToUInt for T
where
    <T as typenum::ToUInt>::Output: Unsigned,
{
    type Output = <T as typenum::ToUInt>::Output;
}

pub type U<const N: usize> = <Const<N> as ToUInt>::Output;
