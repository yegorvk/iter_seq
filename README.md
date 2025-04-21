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
use iter_seq::{Sequence, seq};

fn main() {
    let odd_squares = seq::from_fn(|i| 2 * i as u32 + 1).map(|i| i * i);

    let arr: [u32; 128] = odd_squares.take_exact_s::<128>()
        .collect_array();

    for (i, x) in arr.iter().enumerate() {
        let j = 2 * i as u32 + 1;
        assert_eq!(j * j, x);
    }
}
```