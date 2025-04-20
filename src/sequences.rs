use crate::{DynamicSize, InfiniteSize, Sequence, SizeKind, StaticSize, ToUInt, U};
use core::{array, iter, slice};
use typenum::Const;

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

unsafe impl<I: IntoIterator> Sequence for IterSeq<I> {
    type Item = I::Item;
    type Iter = I::IntoIter;

    type MinSize = DynamicSize;
    type MaxSize = DynamicSize;

    #[inline]
    fn into_iter(self) -> Self::Iter {
        I::into_iter(self.iter)
    }

    #[inline]
    fn min_size(&self) -> SizeKind {
        SizeKind::Finite(0)
    }

    #[inline]
    fn max_size(&self) -> SizeKind {
        SizeKind::Infinite
    }
}

pub struct ArraySeq<T, const N: usize> {
    arr: [T; N],
}

unsafe impl<T, const N: usize> Sequence for ArraySeq<T, N>
where
    Const<N>: ToUInt,
{
    type Item = T;
    type Iter = array::IntoIter<T, N>;

    type MinSize = StaticSize<U<N>>;
    type MaxSize = StaticSize<U<N>>;

    #[inline]
    fn into_iter(self) -> Self::Iter {
        self.arr.into_iter()
    }

    #[inline]
    fn min_size(&self) -> SizeKind {
        SizeKind::Finite(N)
    }

    #[inline]
    fn max_size(&self) -> SizeKind {
        SizeKind::Finite(N)
    }
}

pub struct ArraySliceSeq<'a, T, const N: usize> {
    arr: &'a [T; N],
}

unsafe impl<'a, T, const N: usize> Sequence for ArraySliceSeq<'a, T, N>
where
    Const<N>: ToUInt,
{
    type Item = &'a T;
    type Iter = slice::Iter<'a, T>;

    type MinSize = StaticSize<U<N>>;
    type MaxSize = StaticSize<U<N>>;

    #[inline]
    fn into_iter(self) -> Self::Iter {
        self.arr.iter()
    }

    #[inline]
    fn min_size(&self) -> SizeKind {
        SizeKind::Finite(N)
    }

    #[inline]
    fn max_size(&self) -> SizeKind {
        SizeKind::Finite(N)
    }
}

pub struct ArrayMutSliceSeq<'a, T, const N: usize> {
    arr: &'a mut [T; N],
}

unsafe impl<'a, T, const N: usize> Sequence for ArrayMutSliceSeq<'a, T, N>
where
    Const<N>: ToUInt,
{
    type Item = &'a mut T;
    type Iter = slice::IterMut<'a, T>;

    type MinSize = StaticSize<U<N>>;
    type MaxSize = StaticSize<U<N>>;

    #[inline]
    fn into_iter(self) -> Self::Iter {
        self.arr.iter_mut()
    }

    #[inline]
    fn min_size(&self) -> SizeKind {
        SizeKind::Finite(N)
    }

    #[inline]
    fn max_size(&self) -> SizeKind {
        SizeKind::Finite(N)
    }
}

pub struct Repeat<T: Clone = ()> {
    elem: T,
}

unsafe impl<T: Clone> Sequence for Repeat<T> {
    type Item = T;
    type Iter = iter::Repeat<T>;

    type MinSize = InfiniteSize;
    type MaxSize = InfiniteSize;

    #[inline]
    fn into_iter(self) -> Self::Iter {
        iter::repeat(self.elem)
    }

    #[inline]
    fn min_size(&self) -> SizeKind {
        SizeKind::Infinite
    }

    #[inline]
    fn max_size(&self) -> SizeKind {
        SizeKind::Infinite
    }
}

#[inline]
pub fn repeat<T: Clone>(elem: T) -> Repeat<T> {
    Repeat { elem }
}

pub trait IntoIteratorExt {
    fn iter_seq(self) -> IterSeq<Self>
    where
        Self: Sized;
}

impl<I: IntoIterator> IntoIteratorExt for I {
    #[inline]
    fn iter_seq(self) -> IterSeq<Self>
    where
        Self: Sized,
    {
        IterSeq { iter: self }
    }
}

pub trait ArrayExt<T, const N: usize> {
    fn into_seq(self) -> ArraySeq<T, N>;
    fn as_seq(&self) -> ArraySliceSeq<T, N>;
    fn as_seq_mut(&mut self) -> ArrayMutSliceSeq<T, N>;
}

impl<T, const N: usize> ArrayExt<T, N> for [T; N] {
    #[inline]
    fn into_seq(self) -> ArraySeq<T, N> {
        ArraySeq { arr: self }
    }

    #[inline]
    fn as_seq(&self) -> ArraySliceSeq<T, N> {
        ArraySliceSeq { arr: self }
    }

    #[inline]
    fn as_seq_mut(&mut self) -> ArrayMutSliceSeq<T, N> {
        ArrayMutSliceSeq { arr: self }
    }
}
