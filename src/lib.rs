#![no_std]

/// Stateless, transformable, abstract sequence of values.
///
/// This crate provides a mechanism for working with abstract *stateless*
/// sequences of arbitrary values. In contrast, standard iterators are
/// stateful—that is, their state can be changed by calling `next`.
///
/// One significant limitation of the stateful model is its inability to encode
/// compile-time invariants, which can lead to unnecessary overhead that
/// the compiler often cannot reliably optimize away. This crate provides
/// a "wrapper" around standard iterators that must be irreversibly
/// converted into an iterator before its elements can be consumed.
///
/// # Example
/// ```
/// use iter_seq::{Sequence, const_repeat};
///
/// let odd_squares = const_repeat()
///     .enumerate()
///     .map(|(i, _)| i as u32)
///     .map(|n| (n + 1) * (n + 1));
///
/// let arr: [u32; 128] = odd_squares.const_take_exact::<128>()
///     .collect_array();
///
/// for (i, n) in arr.iter().enumerate() {
///     assert_eq!((i as u32 + 1) * (i as u32 + 1), *n);
/// }
///
/// ```
use core::marker::PhantomData;
use core::{array, iter, slice};

/// Represents a stateless abstract sequence of values.
///
/// This trait closely resembles `Iterator` in terms of functionality but unlike
/// the latter, it cannot yield its elements directly. Instead, it must first be
/// irreversibly converted into an iterator using `into_iter`.
///
/// This design allows a `Sequence` to encode additional invariants, such as a
/// constant size, which is not possible with standard iterators.
pub trait Sequence {
    type Item;
    type Iter: Iterator<Item = Self::Item>;

    /// Converts this sequence into a (stateful) iterator.
    fn into_iter(self) -> Self::Iter;

    /// Collects this sequence's elements into an array.
    #[inline]
    fn collect_array<const N: usize>(self) -> [Self::Item; N]
    where
        Self: Sized + ConstMinLen<N>,
    {
        let mut iter = self.into_iter();

        array::from_fn(|_| {
            // SAFETY: the invariant of `ConstMinLen` guarantees that
            // the iterator will always produce at least `N` elements.
            unsafe { iter.next().unwrap_unchecked() }
        })
    }

    /// Returns a new sequence that transforms every element of the original
    /// sequence using `f`.
    #[inline]
    fn map<F, B>(self, f: F) -> Map<Self, F>
    where
        Self: Sized,
        F: FnMut(Self::Item) -> B,
    {
        Map { seq: self, f }
    }

    /// Returns a new sequence that yields the current iteration index
    /// together with every element.
    #[inline]
    fn enumerate(self) -> Enumerate<Self>
    where
        Self: Sized,
    {
        Enumerate { seq: self }
    }

    /// Returns a new sequence that yields exactly `N` first elements of the original sequence.
    #[inline]
    fn const_take_exact<const N: usize>(self) -> ConstTakeExact<Self, N>
    where
        Self: Sized + ConstMinLen<N>,
    {
        ConstTakeExact { seq: self }
    }
}

/// A `Sequence` that is guaranteed to yield *at least* `N` elements.
///
/// # Safety
/// Implementing this trait is sound only if the sequence always produces
/// at least `N` elements when no panics occur.
pub unsafe trait ConstMinLen<const N: usize>: Sequence {}

/// A `Sequence` that is guaranteed to yield *at most* `N` elements.
///
/// # Safety
/// Implementing this trait is sound only if the sequence always produces at
/// most `N` elements.
pub unsafe trait ConstMaxLen<const N: usize>: Sequence {}

/// A `Sequence` that is guaranteed to yield elements indefinitely as long as
/// no panics occur.
///
/// # Safety
/// Implementing this trait is sound only if the sequence indefinitely yields
/// elements as long as no panics occur.
unsafe trait InfiniteLen: Sequence {}

// SAFETY: an infinite sequence produces elements indefinitely.
unsafe impl<S: InfiniteLen, const N: usize> ConstMinLen<N> for S {}

/// A `Sequence` that is guaranteed to yield *exactly* `N` elements.
///
/// # Safety
/// Implementing this trait is sound only if the sequence always produces
/// exactly `N` elements.
pub unsafe trait ConstLen<const N: usize>: ConstMinLen<N> + ConstMaxLen<N> {}

unsafe impl<T, const N: usize> ConstLen<N> for T where T: ConstMinLen<N> + ConstMaxLen<N> {}

/// Represents a type that can be converted into a sequence.
///
/// The motivation behind this trait is to avoid directly implementing
/// `Sequence` for builtin types, which could lead to ambiguities for
/// end users because of method name collisions.
pub trait IntoSequence {
    type Item;
    type Sequence: Sequence<Item = Self::Item>;

    /// Converts `self` into a sequence.
    fn into_sequence(self) -> Self::Sequence;
}

/// Allowed borrowing `self` as a sequence of values owned by `self`.
pub trait AsSequence {
    type Item;

    type Sequence<'a>: Sequence<Item = &'a Self::Item>
    where
        Self: 'a,
        Self::Item: 'a;

    fn as_sequence(&self) -> Self::Sequence<'_>;
}

/// Allowed borrowing `self` mutably as a sequence of values owned by `self`.
pub trait AsSequenceMut {
    type Item;

    type Sequence<'a>: Sequence<Item = &'a mut Self::Item>
    where
        Self: 'a,
        Self::Item: 'a;

    fn as_sequence_mut(&mut self) -> Self::Sequence<'_>;
}

/// A sequence that transforms every element of the original sequence using `f`.
///
/// This struct is created by the [`map`](Sequence::map) method on [`Sequence`].
pub struct Map<S, F> {
    seq: S,
    f: F,
}

impl<S, F, B> Sequence for Map<S, F>
where
    S: Sequence,
    F: FnMut(S::Item) -> B,
{
    type Item = B;
    type Iter = iter::Map<S::Iter, F>;

    #[inline]
    fn into_iter(self) -> Self::Iter {
        self.seq.into_iter().map(self.f)
    }
}

unsafe impl<S, F, B, const N: usize> ConstMinLen<N> for Map<S, F>
where
    S: Sequence + ConstMinLen<N>,
    F: FnMut(S::Item) -> B,
{
}

unsafe impl<S, F, B, const N: usize> ConstMaxLen<N> for Map<S, F>
where
    S: Sequence + ConstMaxLen<N>,
    F: FnMut(S::Item) -> B,
{
}

/// A sequence that yields the current iteration index for every element.
pub struct Enumerate<S> {
    seq: S,
}

impl<S: Sequence> Sequence for Enumerate<S> {
    type Item = (usize, S::Item);
    type Iter = iter::Enumerate<S::Iter>;

    #[inline]
    fn into_iter(self) -> Self::Iter {
        self.seq.into_iter().enumerate()
    }
}

unsafe impl<S, const N: usize> ConstMinLen<N> for Enumerate<S> where S: Sequence + ConstMinLen<N> {}
unsafe impl<S, const N: usize> ConstMaxLen<N> for Enumerate<S> where S: Sequence + ConstMaxLen<N> {}

pub struct ConstTakeExact<S, const N: usize> {
    seq: S,
}

impl<S, const N: usize> Sequence for ConstTakeExact<S, N>
where
    S: Sequence + ConstMinLen<N>,
{
    type Item = S::Item;
    type Iter = iter::Take<S::Iter>;

    #[inline]
    fn into_iter(self) -> Self::Iter {
        self.seq.into_iter().take(N)
    }
}

unsafe impl<S, const N: usize> ConstMinLen<N> for ConstTakeExact<S, N> where
    S: Sequence + ConstMinLen<N>
{
}
unsafe impl<S, const N: usize> ConstMaxLen<N> for ConstTakeExact<S, N> where
    S: Sequence + ConstMinLen<N>
{
}

/// A sequence created from an iterator.
pub struct IterSeq<I> {
    iter: I,
}

impl<I> IterSeq<I> {
    #[inline]
    pub fn into_inner(self) -> I {
        self.iter
    }
}

impl<I: IntoIterator> Sequence for IterSeq<I> {
    type Item = I::Item;
    type Iter = I::IntoIter;

    #[inline]
    fn into_iter(self) -> Self::Iter {
        I::into_iter(self.iter)
    }
}

impl<I: IntoIterator> IntoSequence for I {
    type Item = I::Item;
    type Sequence = IterSeq<I>;

    #[inline]
    fn into_sequence(self) -> Self::Sequence {
        IterSeq { iter: self }
    }
}

// SAFETY: arrays have a constant length.
unsafe impl<T, const N: usize> ConstMinLen<N> for IterSeq<[T; N]> {}

// SAFETY: arrays have a constant length.
unsafe impl<T, const N: usize> ConstMaxLen<N> for IterSeq<[T; N]> {}

/// A sequence created from an iterator over immutably borrowed values.
pub struct BorrowedIterSeq<I, T> {
    iter: I,
    _owner: PhantomData<fn() -> T>,
}

impl<I: IntoIterator, T> Sequence for BorrowedIterSeq<I, T> {
    type Item = I::Item;
    type Iter = I::IntoIter;

    #[inline]
    fn into_iter(self) -> Self::Iter {
        I::into_iter(self.iter)
    }
}

type BorrowedArraySeq<'a, T, const N: usize> = BorrowedIterSeq<slice::Iter<'a, T>, [T; N]>;

unsafe impl<'a, T, const N: usize> ConstMinLen<N> for BorrowedArraySeq<'a, T, N> {}
unsafe impl<'a, T, const N: usize> ConstMaxLen<N> for BorrowedArraySeq<'a, T, N> {}

/// A sequence created from an iterator over mutably borrowed values.
pub struct BorrowedMutIterSeq<I, T> {
    iter: I,
    _owner: PhantomData<fn() -> T>,
}

impl<I: IntoIterator, T> Sequence for BorrowedMutIterSeq<I, T> {
    type Item = I::Item;
    type Iter = I::IntoIter;

    #[inline]
    fn into_iter(self) -> Self::Iter {
        I::into_iter(self.iter)
    }
}

type BorrowedMutArraySeq<'a, T, const N: usize> = BorrowedMutIterSeq<slice::IterMut<'a, T>, [T; N]>;

unsafe impl<'a, T, const N: usize> ConstMinLen<N> for BorrowedMutArraySeq<'a, T, N> {}
unsafe impl<'a, T, const N: usize> ConstMaxLen<N> for BorrowedMutArraySeq<'a, T, N> {}

impl<T, const N: usize> AsSequence for [T; N] {
    type Item = T;

    type Sequence<'a>
        = BorrowedArraySeq<'a, T, N>
    where
        T: 'a;

    #[inline]
    fn as_sequence(&self) -> Self::Sequence<'_> {
        BorrowedArraySeq {
            iter: self.iter(),
            _owner: PhantomData,
        }
    }
}

impl<T, const N: usize> AsSequenceMut for [T; N] {
    type Item = T;

    type Sequence<'a>
        = BorrowedMutArraySeq<'a, T, N>
    where
        T: 'a;

    #[inline]
    fn as_sequence_mut(&mut self) -> Self::Sequence<'_> {
        BorrowedMutArraySeq {
            iter: self.iter_mut(),
            _owner: PhantomData,
        }
    }
}

pub struct ConstRepeat;

impl Sequence for ConstRepeat {
    type Item = ();
    type Iter = iter::Repeat<()>;

    #[inline]
    fn into_iter(self) -> Self::Iter {
        iter::repeat(())
    }
}

// SAFETY: `ConstRepeat` uses `iter::repeat`, which yields elements indefinitely.
// It is not in general a good idea to rely on safe code to uphold unsafe
// invariants, but in this specific case the "safe" code comes from the
// standard library and the invariant is trivial.
unsafe impl InfiniteLen for ConstRepeat {}

/// Creates a new sequence that indefinitely yields empty tuples.
#[inline]
pub fn const_repeat() -> ConstRepeat {
    ConstRepeat
}

#[cfg(test)]
mod tests {
    use crate::{const_repeat, AsSequence, IntoSequence, Sequence};
    use core::iter::zip;
    use itertools::Itertools;

    #[test]
    fn iter_seq() {
        let even = (0..10).step_by(2).into_sequence();

        for (i, n) in even.enumerate().into_iter() {
            assert_eq!(2 * i, n);
        }
    }

    #[test]
    fn fibonacci() {
        let mut a = 0u64;
        let mut b = 1u64;

        let fib = const_repeat()
            .const_take_exact::<64>()
            .map(|()| {
                let c = a + b;
                a = b;
                b = c;
                a
            })
            .collect_array();

        for (a, b, c) in fib.iter().tuple_windows() {
            assert_eq!(*c, *a + *b);
        }

        let fib2 = fib
            .as_sequence()
            .map(|n| (*n as u128) * (*n as u128))
            .collect_array();

        for (a, b) in zip(&fib, &fib2) {
            assert_eq!((*a as u128) * (*a as u128), *b);
        }
    }
}
