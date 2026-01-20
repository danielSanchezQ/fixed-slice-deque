# fixed-slice-deque

[![MIT licensed](https://img.shields.io/badge/license-MIT-blue.svg)](./LICENSE)
[![GHA Build Status](https://github.com/danielsanchezq/fixed-slice-deque/workflows/CI/badge.svg)](https://github.com/danielsanchezq/fixed-slice-deque/actions?query=workflow%3ACI)
[![Docs Badge](https://docs.rs/fixed-slice-deque/badge.svg)](https://docs.rs/fixed-slice-deque)
[![Crates.io](https://img.shields.io/crates/v/fixed-slice-deque)](https://crates.io/crates/fixed-slice-deque)

### Add the library dependency
```toml
[dependencies]
fixed-slice-deque = "0.1.0-beta3"
```


## Explanation:

A fixed size double-ended queue that `Deref`s into a slice.
For keeping the fixed queue size items pushed out of bounds are pop and returned in inserting
operations.

### Example:
 Initialize state, empty, with fixed size of `3`
 ```txt
 `X = None`
 +---+---+---+
 | X | X | X |
 +---+---+---+
```

 Pushing `1` to the back, since it is empty, `1` is the only item in the deque  
 ```txt
 => push_back(1)

 +---+---+---+
 | 1 | X | X |
 +---+---+---+
```

 Push `2` to the front (left)

 ```txt
 => push_front(2)

 +---+---+---+
 | 2 | 1 | X |
 +---+---+---+
```

 Push again to the back, a single `3`. The deque now **is full**

 ```txt
 => push_back(3)

 +---+---+---+
 | 2 | 1 | 3 |
 +---+---+---+
```

 We try to add a new item at the back, but we would have one extra, the first item (`2`) is pop
 to the left and returned. We keep the elements and the fixed size

 ```txt
 => push_back(4)

 +---+---+---+
 | 1 | 3 | 4 | => return Some(2)
 +---+---+---+
```

 The same happens when pushing to the front again, the back-most (right) item is pop and returned

 ```txt
 => push_front(5)

 +---+---+---+
 | 5 | 1 | 3 | => return Some(4)
 +---+---+---+
```

 It is implemented as a wrapper over [**`VecDeque`**](https://doc.rust-lang.org/std/collections/struct.VecDeque.html)

 This is heavely inspired by `SliceDeque` and almos every orignal `SliceDeque` method is implemented.

## License

This project is licensed under either of

* Apache License, Version 2.0, (LICENSE-APACHE or http://www.apache.org/licenses/LICENSE-2.0)
* MIT license (LICENSE-MIT or http://opensource.org/licenses/MIT)

at your option.

## Contribution

Unless you explicitly state otherwise, any contribution intentionally submitted
for inclusion in SliceDeque by you, as defined in the Apache-2.0 license, shall be
dual licensed as above, without any additional terms or conditions.
