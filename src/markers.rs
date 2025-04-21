use crate::{IsGreaterOrEqual, IsLessOrEqual, Sequence, Size, ConstSize, ToUInt, U};
use sealed::sealed;
use typenum::{Const, Unsigned};

/// Asserts that a `Sequence` is guaranteed to produce *at least* `N` elements.
///
/// This trait should only be used to constrain parameters
/// to allow maximum flexibility for the user.
///
/// # Safety
/// Implementing this trait is sound only if the sequence always produces
/// at least `N` elements, unless a panic occurs.
#[sealed]
pub unsafe trait LowerBound<N: Unsigned>: Sequence {}

#[rustfmt::skip]
#[sealed]
unsafe impl<S: Sequence, N: Unsigned> LowerBound<N> for S
where
    S::MinSize: IsGreaterOrEqual<ConstSize<N>>,
{}

/// Asserts that a `Sequence` is guaranteed to produce *at most* `N` elements.
///
/// This trait should only be used to constrain parameters
/// to allow maximum flexibility for the user.
///
/// # Safety
/// Implementing this trait is sound only if the sequence always produces
/// at most `N` elements, unless a panic occurs.
#[sealed]
pub unsafe trait UpperBound<N: Unsigned>: Sequence {}

#[rustfmt::skip]
#[sealed]
unsafe impl<S: Sequence, N: Unsigned> UpperBound<N> for S
where
    S::MinSize: IsLessOrEqual<ConstSize<N>>,
{}

/// The same as [`LowerBound`], but uses const generics instead of type level integers.
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

/// The same as [`UpperBound`], but uses const generics instead of type level integers.
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

/// Constraints `min_size` of a `Sequence`.
///
/// This trait should be used to constrain the result, unlike [`LowerBound`].
#[sealed]
pub trait MinSize<D: Size>: Sequence<MinSize = D> {}

#[rustfmt::skip]
#[sealed]
impl<S, D> MinSize<D> for S
where
    S: Sequence<MinSize = D>,
    D: Size,
{}

/// Constraints `max_size` of a `Sequence`.
///
/// This trait should be used to constrain the result, unlike [`UpperBound`].
#[sealed]
pub trait MaxSize<D: Size>: Sequence<MaxSize = D> {}

#[rustfmt::skip]
#[sealed]
impl<S, D> MaxSize<D> for S
where
    S: Sequence<MaxSize = D>,
    D: Size,
{}

/// Constraints `min_size` of a `Sequence` to a constant value.
///
/// This trait should be used to constrain the result, unlike [`LowerBound`].
#[sealed]
pub trait ConstMinSize<N: Unsigned>: Sequence<MinSize = ConstSize<N>> {}

#[rustfmt::skip]
#[sealed]
impl<S, N> ConstMinSize<N> for S 
where
    S: Sequence<MinSize = ConstSize<N>>,
    N: Unsigned,
{}

/// Constraints `max_size` of a `Sequence` to a constant value.
///
/// This trait should be used to constrain the result, unlike [`UpperBound`].
#[sealed]
pub trait ConstMaxSize<N: Unsigned>: Sequence<MaxSize = ConstSize<N>> {}

#[rustfmt::skip]
#[sealed]
impl<S, N> ConstMaxSize<N> for S 
where
    S: Sequence<MaxSize = ConstSize<N>>,
    N: Unsigned,
{}

/// The same as [`ConstMinSize`], but uses const generics instead of type level integers.
#[rustfmt::skip]
#[sealed]
pub trait WithConstMinSize<const N: usize>: ConstMinSize<U<N>>
where
    Const<N>: ToUInt,
{}

#[rustfmt::skip]
#[sealed]
impl<S: ConstMinSize<U<N>>, const N: usize> WithConstMinSize<N> for S 
where
    Const<N>: ToUInt,
{}

/// The same as [`ConstMaxSize`], but uses const generics instead of type level integers.
#[rustfmt::skip]
#[sealed]
pub trait WithConstMaxSize<const N: usize>: ConstMaxSize<U<N>>
where
    Const<N>: ToUInt,
{}

#[rustfmt::skip]
#[sealed]
impl<S: ConstMaxSize<U<N>>, const N: usize> WithConstMaxSize<N> for S 
where
    Const<N>: ToUInt,
{}

/// Constraints `min_size` and `max_size` of a `Sequence`.
#[sealed]
trait ExactSize<D: Size>: Sequence<MinSize = D, MaxSize = D> {}

#[rustfmt::skip]
#[sealed]
impl<S, D> ExactSize<D> for S 
where
    S: Sequence<MinSize = D, MaxSize = D>,
    D: Size,
{}

/// Constraints `min_size` and `max_size` of a `Sequence` to a constant value.
#[allow(private_bounds)]
#[sealed]
pub trait ExactConstSize<N: Unsigned>: ExactSize<ConstSize<N>> {}

#[rustfmt::skip]
#[sealed]
impl<S, N> ExactConstSize<N> for S 
where
    S: ExactSize<ConstSize<N>>,
    N: Unsigned,
{}

/// The same as [`ExactConstSize`], but uses const generics instead of type level integers.
#[sealed]
pub trait WithConstSize<const N: usize>: ExactConstSize<U<N>>
where
    Const<N>: ToUInt,
{
}

#[rustfmt::skip]
#[sealed]
impl<S, const N: usize> WithConstSize<N> for S 
where
    S: ExactConstSize<U<N>>,
    Const<N>: ToUInt,
{}
