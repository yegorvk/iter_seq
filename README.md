# iter_seq

Stateless, transformable, abstract sequence of values.

This crate provides a mechanism for working with abstract *stateless*
sequences of arbitrary values. In contrast, standard iterators are
stateful—that is, their state can be changed by calling `next`.

One significant limitation of the stateful model is its inability to encode
compile-time invariants, which can lead to unnecessary overhead that
the compiler often cannot reliably optimize away. This crate provides
a "wrapper" around standard iterators that must be irreversibly
converted into an iterator before its elements can be consumed.

# Example

```rust
use iter_seq::{const_repeat, Sequence};

fn main() {
    let odd_squares = const_repeat()
        .enumerate()
        .map(|(i, _)| i as u32)
        .map(|n| (n + 1) * (n + 1));

    let arr: [u32; 128] = odd_squares.const_take_exact::<128>()
        .collect_array();

    for (i, n) in arr.iter().enumerate() {
        assert_eq!((i as u32 + 1) * (i as u32 + 1), *n);
    }
}
```