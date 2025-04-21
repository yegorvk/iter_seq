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
//!
//!
//! use iter_seq::{Sequence, seq};
//!
//! let odd_squares = seq::from_fn(|i| 2 * i as u32 + 1).map(|i| i * i);
//!
//! let arr: [u32; 128] = odd_squares.take_exact_s::<128>()
//!     .collect_array();
//!
//! for (i, n) in arr.iter().enumerate() {
//!     let j = 2 * i as u32 + 1;
//!     assert_eq!(j * j, *n);
//! }
//!
//! ```

#[cfg(test)]
extern crate std;

pub mod adapters;
pub mod markers;
pub mod seq;
mod size;
mod utils;

use crate::adapters::{Enumerate, FlatMap, Flatten, Map, TakeExactS, TakeExactSTn};
use crate::markers::WithLowerBound;
use core::marker::PhantomData;
use core::mem::MaybeUninit;
use core::ptr::{drop_in_place, NonNull};
use core::{array, mem};
use typenum::{Const, Unsigned};

pub use crate::size::*;
pub use crate::utils::{ToUInt, U};

/// Represents a stateless abstract sequence of values.
///
/// This trait closely resembles `Iterator` in terms of functionality, but unlike
/// the latter, it cannot yield its elements directly. Instead, it must first be
/// irreversibly converted into an iterator using `into_iter`.
///
/// This design allows a `Sequence` to encode additional invariants, such as a
/// constant size, which is not possible with standard iterators.
///
/// # Safety
/// This trait is unsafe because there are certain invariants on
/// `MinSize`/`min_size` and `MaxSize`/`max_size` that must be
/// upheld to avoid causing undefined behavior.
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

    const MIN_SIZE: Option<SizeKind> = Self::MinSize::SIZE;
    const MAX_SIZE: Option<SizeKind> = Self::MaxSize::SIZE;

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
            if const { mem::needs_drop::<Self::Item>() } {
                struct Guard<T> {
                    filled: usize,
                    _t: PhantomData<T>,
                }

                impl<T> Drop for Guard<T> {
                    fn drop(&mut self) {
                        for _ in 0..self.filled {
                            let elem_ptr: *mut T = NonNull::dangling().as_ptr();
                            // SAFETY: a dangling pointer is always valid for zero-sized types.
                            unsafe { drop_in_place(elem_ptr) }
                        }
                    }
                }

                let mut guard: Guard<Self::Item> = Guard {
                    filled: 0,
                    _t: PhantomData,
                };

                for _ in 0..N {
                    // IMPORTANT!: we should not drop the element here,
                    // even though it is a zero-sized type.
                    mem::forget(next_elem());
                    guard.filled += 1;
                }

                mem::forget(guard);
            } else {
                for _ in 0..N {
                    _ = next_elem();
                }
            }

            return;
        }

        let ptr: *mut Self::Item = out.as_mut_ptr().cast();

        if const { mem::needs_drop::<Self::Item>() } {
            struct Guard<T> {
                ptr: *mut T,
                filled: usize,
            }

            impl<T> Drop for Guard<T> {
                fn drop(&mut self) {
                    for i in 0..self.filled {
                        let slot = unsafe { self.ptr.add(i) };
                        unsafe { drop_in_place(slot) };
                    }
                }
            }

            let mut guard = Guard { ptr, filled: 0 };

            while guard.filled < N {
                // This could panic.
                let elem = next_elem();
                let slot = unsafe { guard.ptr.add(guard.filled) };
                unsafe { slot.write(elem) }
                guard.filled += 1;
            }

            mem::forget(guard);
        } else {
            for i in 0..N {
                // We don't care if it panics.
                let elem = next_elem();
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

/// A sequence that is guaranteed to produce elements indefinitely, unless a panic occurs.
pub trait InfiniteSequence: Sequence<MinSize = InfiniteSize> {}

impl<S: Sequence<MinSize = InfiniteSize>> InfiniteSequence for S {}

/// Collects a sequence into an array in the most efficient way possible,
/// ensuring that no unnecessary memory copies will occur.
///
/// The downside is that the caller doesn't own the resulting array because
/// `$name` only gets assigned a mutable reference to it.
#[macro_export]
macro_rules! collect_array {
    ($name:tt: $ty:ty, $seq:expr) => {
        // This is effectively private due to macro hygiene.
        let mut buf: ::core::mem::MaybeUninit<$ty> = ::core::mem::MaybeUninit::uninit();
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
    use super::seq::{ArrayExt, IntoIteratorExt};
    use super::*;
    use crate::markers::WithConstSize;
    use itertools::Itertools;
    use std::hint::black_box;
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

        let fib: [u64; 64] = seq::from_fn(|_| {
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
        let prog = seq::from_fn(|i| seq::from_fn(move |j| (i, j)).take_exact_s::<64>())
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
    fn collect_array_macro() {
        let seq = seq::from_fn(|_| black_box(1)).take_exact_s::<1000>();
        collect_array!(arr: [_; 900], seq);
        assert_eq!(arr, &mut [1; 900]);
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

        let my_seq = seq::from_fn(|i| {
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
        let seq = seq::repeat(()).take_exact_s::<1000>();
        collect_array!(arr: [_; 900], seq);
        assert_eq!(arr, &mut [(); 900]);
    }

    #[test]
    fn collect_array_macro_zst_panic() {
        static DROP_COUNTER: Mutex<usize> = Mutex::new(0usize);

        struct Value;

        impl Drop for Value {
            fn drop(&mut self) {
                let mut guard = DROP_COUNTER.lock().unwrap();
                *guard += 1;
            }
        }

        let my_seq = seq::from_fn(|i| {
            if i < 7 {
                Value
            } else {
                panic!();
            }
        });

        let unwind = catch_unwind(|| {
            collect_array!(_: [_; 8], my_seq);
        });

        assert!(unwind.is_err());
        assert_eq!(*DROP_COUNTER.lock().unwrap(), 7);
    }

    #[test]
    fn ret_seq() {
        fn odds() -> impl Sequence<Item = u32> + WithConstSize<1024> {
            seq::from_fn(|i| 2 * i as u32 + 1).take_exact_s::<1024>()
        }

        for (i, x) in odds().into_iter().enumerate() {
            assert_eq!(i as u32 * 2 + 1, x);
        }
    }
}
