#![no_std]

//! Stateless, transformable, abstract sequences of values.
//!
//! This crate provides a mechanism for working with abstract *stateless*
//! sequences of arbitrary values. In contrast, standard iterators are
//! stateful—that is, their state can be changed by calling `next`.
//!
//! One significant limitation of the stateful model is its inability to encode
//! compile-time invariants, which can lead to unnecessary overhead that
//! the compiler often cannot reliably optimize away. This crate provides
//! a "wrapper" around standard iterators that must be irreversibly
//! converted into an iterator before its elements can be consumed.
//!
//! # Example
//! ```
//! use iter_seq::{Sequence, repeat};
//!
//! let odd_squares = repeat(())
//!     .enumerate()
//!     .map(|(i, _)| i as u32)
//!     .map(|n| (n + 1) * (n + 1));
//!
//! let arr: [u32; 128] = odd_squares.take_exact_s::<128>()
//!     .collect_array();
//!
//! for (i, n) in arr.iter().enumerate() {
//!     assert_eq!((i as u32 + 1) * (i as u32 + 1), *n);
//! }
//!
//! ```

#[cfg(test)]
extern crate std;

mod adapters;
mod bounds;
mod sequences;
mod size;
mod utils;

use core::marker::PhantomData;
use core::mem::MaybeUninit;
use core::{array, mem};

pub use crate::adapters::{Enumerate, FlatMap, Flatten, Map, TakeExactS, TakeExactSTn};
pub use crate::bounds::{LowerBound, UpperBound, WithLowerBound, WithUpperBound};
pub use crate::sequences::{
    from_fn, repeat, ArrayExt, ArrayMutSliceSeq, ArraySeq, ArraySliceSeq, FromFn, IntoIteratorExt,
    IterSeq, Repeat,
};
pub use crate::size::{
    DynamicSize, InfiniteSize, IsDynamic, IsEqual, IsFinite, IsGreaterOrEqual, IsGreaterThan,
    IsInfinite, IsLessOrEqual, IsLessThan, Size, SizeKind, StaticSize,
};
pub use crate::utils::{ToUInt, U};
pub use typenum;
pub use typenum::{Const, Unsigned};

/// Represents a stateless abstract sequence of values.
///
/// This trait closely resembles `Iterator` in terms of functionality but unlike
/// the latter, it cannot yield its elements directly. Instead, it must first be
/// irreversibly converted into an iterator using `into_iter`.
///
/// This design allows a `Sequence` to encode additional invariants, such as a
/// constant size, which is not possible with standard iterators.
///
/// # Safety
/// This crates is unsafe, because there are certain invariants on
/// `MinSize`/`min_size` and `MaxSize`/`max_size` that must be
/// upheld in order to avoid causing undefined behaviours.
pub unsafe trait Sequence {
    type Item;
    type Iter: Iterator<Item = Self::Item>;

    /// The minimum size of the sequence.
    ///
    /// # Safety
    /// This value must *never* be greater than the actual minimum possible
    /// number of elements in the sequence, excluding panics.
    type MinSize: Size;

    /// The maximum size of the sequence.
    ///
    /// # Safety
    /// This value must *never* be less than the actual maximum
    /// possible number of elements in the sequence.
    type MaxSize: Size;

    const MIN_SIZE: Option<SizeKind> = Self::MinSize::STATIC_SIZE;
    const MAX_SIZE: Option<SizeKind> = Self::MaxSize::STATIC_SIZE;

    /// Converts this sequence into a (stateful) iterator.
    fn into_iter(self) -> Self::Iter;

    /// Returns the minimum size of the sequence.
    ///
    /// # Safety
    /// This value must *never* be greater than the actual minimum possible
    /// number of elements in the sequence, excluding panics.
    fn min_size(&self) -> SizeKind;

    /// Returns the maximum size of the sequence.
    ///
    /// # Safety
    /// This value must *never* be less than the actual maximum
    /// possible number of elements in the sequence.
    fn max_size(&self) -> SizeKind;

    /// Collects this sequence's elements into an array.
    #[inline(always)]
    fn collect_array<const N: usize>(self) -> [Self::Item; N]
    where
        Self: Sized + WithLowerBound<N>,
        Const<N>: ToUInt,
    {
        let mut iter = self.into_iter();

        array::from_fn(|_| {
            // SAFETY: the invariant of `WithLowerBound` guarantees that
            // the iterator will always produce at least `N` elements.
            unsafe { iter.next().unwrap_unchecked() }
        })
    }

    /// Collects this sequence's elements into an array in place.
    #[inline(always)]
    fn collect_array_in_place<const N: usize>(self, out: &mut MaybeUninit<[Self::Item; N]>)
    where
        Self: Sized + WithLowerBound<N>,
        Const<N>: ToUInt,
    {
        let mut iter = self.into_iter();

        let mut next_elem = || {
            let elem = iter.next();
            debug_assert!(elem.is_some(), "sequence min_size invariant violated");
            // SAFETY: the invariant of `WithLowerBound` guarantees that
            // the iterator will always produce at least `N` elements.
            unsafe { elem.unwrap_unchecked() }
        };

        // Special handling for ZSTs.
        if const { size_of::<Self::Item>() == 0 } {
            for _ in 0..N {
                _ = next_elem();
            }

            return;
        }

        if const { mem::needs_drop::<Self::Item>() } {
            struct DropGuard<'a, T, const N: usize> {
                arr: &'a mut MaybeUninit<[T; N]>,
                filled: usize,
            }

            impl<T, const N: usize> Drop for DropGuard<'_, T, N> {
                fn drop(&mut self) {
                    for i in 0..self.filled {
                        let ptr = self.arr.as_mut_ptr() as *mut T;
                        let slot = unsafe { ptr.add(i) };
                        unsafe { core::ptr::drop_in_place(slot) };
                    }
                }
            }

            let mut guard = DropGuard {
                arr: out,
                filled: 0,
            };

            while guard.filled < N {
                // This could panic.
                let elem = next_elem();
                let ptr: *mut Self::Item = guard.arr.as_mut_ptr().cast();
                let slot = unsafe { ptr.add(guard.filled) };
                unsafe { slot.write(elem) }
                guard.filled += 1;
            }

            mem::forget(guard);
        } else {
            for i in 0..N {
                // We don't care if it panics.
                let elem = next_elem();
                let ptr: *mut Self::Item = out.as_mut_ptr().cast();
                let slot = unsafe { ptr.add(i) };
                unsafe { slot.write(elem) }
            }
        }
    }

    /// Returns a new sequence that transforms every element of
    /// the original sequence using `f`.
    #[inline]
    fn map<F, B>(self, f: F) -> Map<Self, F>
    where
        Self: Sized,
        F: FnMut(Self::Item) -> B,
    {
        Map { seq: self, f }
    }

    /// Returns a new sequence that transforms every element of the original
    /// sequence by calling `f` and then "flattening" the result.
    #[inline]
    fn flat_map<F, U>(self, f: F) -> FlatMap<Self, F>
    where
        Self: Sized,
        U: Sequence,
        F: FnMut(Self::Item) -> U,
    {
        self.map(f).flatten()
    }

    /// "Flattens" the sequence by removing one nesting layer.
    #[inline]
    fn flatten<U>(self) -> Flatten<Self>
    where
        Self: Sequence<Item = U> + Sized,
        U: Sequence,
    {
        Flatten { seq: self }
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

    /// Returns a new sequence that always yields the first exactly `N` elements.
    #[inline]
    fn take_exact_stn<N: Unsigned>(self) -> TakeExactSTn<Self, N>
    where
        Self: Sized,
    {
        TakeExactSTn {
            seq: self,
            _n: PhantomData,
        }
    }

    /// Returns a new sequence that always yields the first exactly `N` elements.
    #[inline]
    fn take_exact_s<const N: usize>(self) -> TakeExactS<Self, N>
    where
        Self: Sized,
        Const<N>: ToUInt,
    {
        self.take_exact_stn::<U<N>>()
    }
}

/// Collects a sequence into an array in the most efficient way possible,
/// ensuring that no unnecessary memory copies will occur.
///
/// The downside is that the consumer doesn't own the resulting array since
/// `$name` only gets assigned a mutable reference to it.
#[macro_export]
macro_rules! collect_array {
    ($name:tt: $ty:ty, $seq:expr) => {
        // This is effectively private due to macro hygiene.
        let mut buf: ::core::mem::MaybeUninit<$ty> = core::mem::MaybeUninit::uninit();
        $crate::Sequence::collect_array_in_place($seq, &mut buf);
        let $name: &mut $ty = unsafe { buf.assume_init_mut() };
    };

    ($buf:expr, $name:tt: $ty:ty, $seq:expr) => {
        // This is effectively private due to macro hygiene.
        let buf = &mut $buf;
        $crate::Sequence::collect_array_in_place($seq, buf);
        let $name: &mut $ty = unsafe { buf.assume_init_mut() };
    };
}

#[cfg(test)]
mod tests {
    use super::*;
    use itertools::Itertools;
    use std::iter::zip;
    use std::panic::catch_unwind;
    use std::sync::Mutex;

    #[test]
    fn iter_seq() {
        let even = (0..10).step_by(2).iter_seq();

        for (i, n) in even.enumerate().into_iter() {
            assert_eq!(2 * i, n);
        }
    }

    #[test]
    fn fibonacci() {
        let mut a = 0u64;
        let mut b = 1u64;

        let fib: [u64; 64] = from_fn(|_| {
            let c = a + b;
            a = b;
            b = c;
            a
        })
        .take_exact_s::<64>()
        .collect_array();

        for (a, b, c) in fib.iter().tuple_windows() {
            assert_eq!(*c, *a + *b);
        }

        let fib2: [u128; 64] = fib
            .as_seq()
            .map(|n| (*n as u128) * (*n as u128))
            .collect_array();

        for (a, b) in zip(&fib, &fib2) {
            assert_eq!((*a as u128) * (*a as u128), *b);
        }
    }

    #[test]
    fn flatten() {
        let prog = from_fn(|i| {
            repeat(())
                .enumerate()
                .map(move |(j, _)| (i, j))
                .take_exact_s::<64>()
        })
        .take_exact_s::<128>()
        .flatten();

        let arr: [(usize, usize); 64 * 128] = prog.collect_array();

        for (i, elem) in arr.iter().enumerate() {
            let x = i / 64;
            let y = i % 64;
            assert_eq!((x, y), *elem);
        }
    }

    #[test]
    fn collect_array_macro_panic() {
        let drop_counter = Mutex::new(0usize);

        struct Value<'a> {
            drop_counter: &'a Mutex<usize>,
        }

        impl Drop for Value<'_> {
            fn drop(&mut self) {
                let mut guard = self.drop_counter.lock().unwrap();
                *guard += 1;
            }
        }

        let my_seq = from_fn(|i| {
            if i < 7 {
                Value {
                    drop_counter: &drop_counter,
                }
            } else {
                panic!();
            }
        });

        let unwind = catch_unwind(|| {
            collect_array!(_: [_; 8], my_seq);
        });

        assert!(unwind.is_err());
        assert_eq!(*drop_counter.lock().unwrap(), 7);
    }

    #[test]
    fn collect_array_macro_zst() {
        let seq = repeat(()).take_exact_s::<1000>();
        collect_array!(arr: [_; 900], seq);
        assert_eq!(arr, &mut [(); 900]);
    }
}
