use crate::size::{IsGreaterOrEqual, IsLessOrEqual};
use crate::{Sequence, ToUInt, U};
use sealed::sealed;
use typenum::{Const, Unsigned};

/// A `Sequence` that is guaranteed to yield *at least* `N` elements,
/// but could yield more.
///
/// # Safety
/// Implementing this trait is sound only if the sequence always produces
/// at least `N` elements when no panics occur.
#[sealed]
pub unsafe trait LowerBound<N: Unsigned>: Sequence {}

/// A `Sequence` that is guaranteed to yield *at most* `N` elements,
/// but could yield less.
///
/// # Safety
/// Implementing this trait is sound only if the sequence always produces at
/// most `N` elements.
#[sealed]
pub unsafe trait UpperBound<N: Unsigned>: Sequence {}

#[rustfmt::skip]
#[sealed]
pub trait WithLowerBound<const N: usize>: LowerBound<U<N>>
where
    Const<N>: ToUInt,
{}

#[rustfmt::skip]
#[sealed]
impl<S, const N: usize> WithLowerBound<N> for S
where
    S: LowerBound<U<N>>,
    Const<N>: ToUInt,
{}

#[rustfmt::skip]
#[sealed]
pub trait WithUpperBound<const N: usize>: UpperBound<U<N>>
where
    Const<N>: ToUInt,
{}

#[rustfmt::skip]
#[sealed]
impl<S, const N: usize> WithUpperBound<N> for S
where
    S: UpperBound<U<N>>,
    Const<N>: ToUInt,
{}

#[rustfmt::skip]
#[sealed]
unsafe impl<S: Sequence, N: Unsigned> LowerBound<N> for S
where
    S::MinSize: IsGreaterOrEqual<N>,
{}

#[rustfmt::skip]
#[sealed]
unsafe impl<S: Sequence, N: Unsigned> UpperBound<N> for S
where
    S::MinSize: IsLessOrEqual<N>,
{}
