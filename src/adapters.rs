use crate::size::flatten_size;
use crate::{FlattenSize, IsGreaterOrEqual, Sequence, Size, SizeKind, StaticSize, ToSize, U};
use core::iter;
use core::marker::PhantomData;
use typenum::Unsigned;

/// A sequence that transforms every element of the original sequence using `f`
pub struct Map<S, F> {
    pub(crate) seq: S,
    pub(crate) f: F,
}

unsafe impl<S, F, B> Sequence for Map<S, F>
where
    S: Sequence,
    F: FnMut(S::Item) -> B,
{
    type Item = B;
    type Iter = iter::Map<S::Iter, F>;

    type MinSize = S::MinSize;
    type MaxSize = S::MaxSize;

    #[inline]
    fn into_iter(self) -> Self::Iter {
        self.seq.into_iter().map(self.f)
    }

    #[inline]
    fn min_size(&self) -> SizeKind {
        self.seq.min_size()
    }

    #[inline]
    fn max_size(&self) -> SizeKind {
        self.seq.max_size()
    }
}

pub type FlatMap<S, F> = Flatten<Map<S, F>>;

/// A sequence that yields the current iteration index for every element.
pub struct Enumerate<S> {
    pub(crate) seq: S,
}

unsafe impl<S: Sequence> Sequence for Enumerate<S> {
    type Item = (usize, S::Item);
    type Iter = iter::Enumerate<S::Iter>;

    type MinSize = S::MinSize;
    type MaxSize = S::MaxSize;

    #[inline]
    fn into_iter(self) -> Self::Iter {
        self.seq.into_iter().enumerate()
    }

    #[inline]
    fn min_size(&self) -> SizeKind {
        self.seq.min_size()
    }

    #[inline]
    fn max_size(&self) -> SizeKind {
        self.seq.max_size()
    }
}

pub struct TakeExactSTn<S, N: Unsigned> {
    pub(crate) seq: S,
    pub(crate) _n: PhantomData<N>,
}

unsafe impl<S: Sequence, N: Unsigned> Sequence for TakeExactSTn<S, N>
where
    S::MinSize: IsGreaterOrEqual<StaticSize<N>>,
{
    type Item = S::Item;
    type Iter = iter::Take<S::Iter>;

    type MinSize = StaticSize<N>;
    type MaxSize = StaticSize<N>;

    #[inline]
    fn into_iter(self) -> Self::Iter {
        self.seq.into_iter().take(N::USIZE)
    }

    #[inline]
    fn min_size(&self) -> SizeKind {
        SizeKind::Finite(N::USIZE)
    }

    #[inline]
    fn max_size(&self) -> SizeKind {
        SizeKind::Finite(N::USIZE)
    }
}

pub type TakeExactS<T, const N: usize> = TakeExactSTn<T, U<N>>;

pub struct Flatten<S> {
    pub(crate) seq: S,
}

unsafe impl<S: Sequence<Item = U>, U: Sequence> Sequence for Flatten<S>
where
    FlattenSize<S::MinSize, U::MinSize>: ToSize,
    FlattenSize<S::MaxSize, U::MaxSize>: ToSize,
{
    type Item = U::Item;
    type Iter = iter::FlatMap<S::Iter, U::Iter, fn(U) -> U::Iter>;

    type MinSize = <FlattenSize<S::MinSize, U::MinSize> as ToSize>::Size;
    type MaxSize = <FlattenSize<S::MaxSize, U::MaxSize> as ToSize>::Size;

    #[inline]
    fn into_iter(self) -> Self::Iter {
        let f: fn(U) -> U::Iter = |seq| seq.into_iter();
        self.seq.into_iter().flat_map(f)
    }

    #[inline]
    fn min_size(&self) -> SizeKind {
        if let Some(inner) = U::MinSize::SIZE {
            flatten_size(self.seq.min_size(), inner)
        } else {
            SizeKind::Finite(0)
        }
    }

    #[inline]
    fn max_size(&self) -> SizeKind {
        if let Some(inner) = U::MaxSize::SIZE {
            flatten_size(self.seq.max_size(), inner)
        } else {
            SizeKind::Infinite
        }
    }
}
