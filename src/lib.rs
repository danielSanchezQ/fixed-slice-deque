//! A fixed size double-ended queue that `Deref`s into a slice.
//! For keeping the fixed queue size items pushed out of bounds are pop and returned in inserting
//! operations.
//!
//! ## Example:
//! ```txt
//! `X = None`
//! +---+---+---+
//! | X | X | X |
//! +---+---+---+
//!
//! => push_back(1)
//!
//! +---+---+---+
//! | 1 | X | X |
//! +---+---+---+
//!
//! => push_front(2)
//!
//! +---+---+---+
//! | 2 | 1 | X |
//! +---+---+---+
//!
//! => push_back(3)
//!
//! +---+---+---+
//! | 2 | 1 | 3 |
//! +---+---+---+
//!
//! => push_back(4)
//!
//! +---+---+---+
//! | 1 | 3 | 4 | => return Some(2)
//! +---+---+---+
//!```
//!
//! It is implemented as a wrapper over [`SliceDeque`] [**`slice-deque`** crate](<https://crates.io/crates/slice-deque>)
//!
//! Almost every orignal [`SliceDeque`] method is wrapped.
//! Please refer to it's twin method [documentation](https://docs.rs/slice-deque/latest/slice_deque/)
//! for internal functionality.

use slice_deque::SliceDeque;
use std::ops::{Deref, DerefMut};
use std::slice;

/// A fixed size double-ended queue that derefs into a slice.
/// It maintains the size by poping out of bounds items in inserting operations.
///
/// It is implemented as a wrapper over [`SliceDeque`]
#[derive(Debug, Clone, Eq, Hash, Default)]
pub struct FixedSliceDeque<T> {
    buffer: SliceDeque<T>,
    capacity: usize,
}

/// Creates a [`FixedSliceDeque`] containing the arguments.
///
/// `fsdeq!` allows `FixedSliceDeque`s to be defined with the same syntax as array
/// expressions. There are two forms of this macro:
///
/// - Create a [`FixedSliceDeque`] containing a given list of elements:
///
/// ```
/// # use fixed_slice_deque::{FixedSliceDeque, fsdeq};
/// # fn main() {
/// let v: FixedSliceDeque<i32> = fsdeq![1, 2, 3];
/// assert_eq!(v[0], 1);
/// assert_eq!(v[1], 2);
/// assert_eq!(v[2], 3);
/// # }
/// ```
///
/// - Create a [`FixedSliceDeque`] from a given element and size:
///
/// ```
/// # use fixed_slice_deque::{FixedSliceDeque, fsdeq};
/// # fn main() {
/// let v = fsdeq![7; 3];
/// assert_eq!(v, [7, 7, 7]);
/// # }
/// ```
///
/// Note that unlike array expressions this syntax supports all elements
/// which implement `Clone` and the number of elements doesn't have to be
/// a constant.
///
/// This will use `clone` to duplicate an expression, so one should be careful
/// using this with types having a nonstandard `Clone` implementation. For
/// example, `fsdeq![Rc::new(1); 5]` will create a deque of five references
/// to the same boxed integer value, not five references pointing to
/// independently boxed integers.
///
/// ```
/// # #[macro_use] extern crate fixed_slice_deque;
/// # use slice_deque::SliceDeque;
/// # use std::rc::Rc;
/// # fn main() {
/// let v = fsdeq![Rc::new(1_i32); 5];
/// let ptr: *const i32 = &*v[0] as *const i32;
/// for i in v.iter() {
///     assert_eq!(Rc::into_raw(i.clone()), ptr);
/// }
/// # }
/// ```
///
/// [`SliceDeque`]: struct.SliceDeque.html
#[macro_export]
macro_rules! fsdeq {
    ($elem:expr; $n:expr) => (
        {
            let mut deq = $crate::FixedSliceDeque::new($n);
            deq.resize($n, $elem);
            deq
        }
    );
    ($($x:expr),*) => (
        {
            let sdeq = ::slice_deque::sdeq![$($x),*];
            let deq = $crate::FixedSliceDeque::from_slice_deque(sdeq);
            deq
        }
    );
    ($($x:expr,)*) => (fsdeq![$($x),*])
}

impl<T> FixedSliceDeque<T> {
    /// Create an empty fixed size deque with capacity to hold `n` elements.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use fixed_slice_deque::FixedSliceDeque;
    /// let deq = FixedSliceDeque::new(10);
    /// # let o: FixedSliceDeque<u32> = deq;
    /// ```
    #[inline]
    pub fn new(size: usize) -> Self {
        Self {
            buffer: SliceDeque::with_capacity(size),
            capacity: size,
        }
    }

    /// Create an new fixed size deque with capacity to hold `n` elements from a [`SliceDeque`].
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use fixed_slice_deque::FixedSliceDeque;
    /// # use slice_deque::sdeq;
    /// let deq = FixedSliceDeque::from_slice_deque(sdeq![1, 2, 3]);
    /// # let o: FixedSliceDeque<u32> = deq;
    /// ```
    pub fn from_slice_deque(deque: SliceDeque<T>) -> Self {
        Self {
            capacity: deque.len(),
            buffer: deque,
        }
    }

    /// Is the ring buffer full ?
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use fixed_slice_deque::FixedSliceDeque;
    /// let mut deq = FixedSliceDeque::new(10);
    /// assert!(!deq.is_full());
    /// # let o: FixedSliceDeque<u32> = deq;
    /// ```
    #[inline]
    pub fn is_full(&self) -> bool {
        self.buffer.len() == self.capacity
    }

    /// Is the ring buffer empty ?
    /// Check if the buffer do not contain any item
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use fixed_slice_deque::FixedSliceDeque;
    /// let mut deq = FixedSliceDeque::new(10);
    /// assert!(deq.is_empty());
    /// # let o: FixedSliceDeque<u32> = deq;
    /// ```
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.buffer.is_empty()
    }

    /// Buffer occupied size
    #[inline]
    pub fn len(&self) -> usize {
        self.buffer.len()
    }

    /// Buffer capacity
    #[inline]
    pub fn capacity(&self) -> usize {
        self.capacity
    }

    /// Extracts a slice containing the entire deque.
    #[inline]
    pub fn as_slice(&self) -> &[T] {
        self.buffer.as_slice()
    }

    /// Extracts a mutable slice containing the entire deque.
    #[inline]
    pub fn as_mut_slice(&mut self) -> &mut [T] {
        self.buffer.as_mut_slice()
    }

    /// Moves all the elements of `other` into `Self`, leaving `other` empty.
    ///
    /// It keeps the internal [`FixedSliceDeque`] capacity. All items that will not fit into the
    /// capacity are truncated from the head.
    ///
    /// # Examples
    ///
    /// ```
    /// # use fixed_slice_deque::{FixedSliceDeque, fsdeq};
    /// # fn main() {
    /// let mut deq = fsdeq![1, 2, 3];
    /// let mut deq2 = fsdeq![4, 5, 6];
    /// deq.append(&mut deq2);
    /// assert_eq!(deq, [4, 5, 6]);
    /// assert_eq!(deq2, []);
    /// # }
    /// ```
    #[inline]
    pub fn append(&mut self, other: &mut Self) {
        if other.len() + self.len() <= self.capacity {
            self.buffer.append(&mut other.buffer);
        } else {
            other
                .buffer
                .truncate_back(other.len() - (self.capacity - self.len()));
            self.buffer.clear();
            self.buffer.append(&mut other.buffer);
        }
        other.buffer.clear();
    }

    /// Provides a reference to the first element, or `None` if the deque is
    /// empty.
    ///
    /// # Examples
    ///
    /// ```
    /// # use fixed_slice_deque::FixedSliceDeque;
    /// let mut deq = FixedSliceDeque::new(3);
    /// assert_eq!(deq.front(), None);
    ///
    /// deq.push_back(1);
    /// deq.push_back(2);
    /// assert_eq!(deq.front(), Some(&1));
    /// deq.push_front(3);
    /// assert_eq!(deq.front(), Some(&3));
    /// ```
    #[inline]
    pub fn front(&self) -> Option<&T> {
        self.buffer.front()
    }

    /// Provides a mutable reference to the first element, or `None` if the
    /// deque is empty.
    ///
    /// # Examples
    ///
    /// ```
    /// # use fixed_slice_deque::FixedSliceDeque;
    /// let mut deq = FixedSliceDeque::new(3);
    /// assert_eq!(deq.front(), None);
    ///
    /// deq.push_back(1);
    /// deq.push_back(2);
    /// assert_eq!(deq.front(), Some(&1));
    /// (*deq.front_mut().unwrap()) = 3;
    /// assert_eq!(deq.front(), Some(&3));
    /// ```
    #[inline]
    pub fn front_mut(&mut self) -> Option<&mut T> {
        self.buffer.front_mut()
    }

    /// Provides a reference to the last element, or `None` if the deque is
    /// empty.
    ///
    /// # Examples
    ///
    /// ```
    /// # use fixed_slice_deque::FixedSliceDeque;
    /// let mut deq = FixedSliceDeque::new(3);
    /// assert_eq!(deq.back(), None);
    ///
    /// deq.push_back(1);
    /// deq.push_back(2);
    /// assert_eq!(deq.back(), Some(&2));
    /// deq.push_front(3);
    /// assert_eq!(deq.back(), Some(&2));
    /// ```
    #[inline]
    pub fn back(&self) -> Option<&T> {
        self.buffer.back()
    }

    /// Provides a mutable reference to the last element, or `None` if the
    /// deque is empty.
    ///
    /// # Examples
    ///
    /// ```
    /// # use fixed_slice_deque::FixedSliceDeque;
    /// let mut deq = FixedSliceDeque::new(3);
    /// assert_eq!(deq.front(), None);
    ///
    /// deq.push_back(1);
    /// deq.push_back(2);
    /// assert_eq!(deq.back(), Some(&2));
    /// (*deq.back_mut().unwrap()) = 3;
    /// assert_eq!(deq.back(), Some(&3));
    /// ```
    #[inline]
    pub fn back_mut(&mut self) -> Option<&mut T> {
        self.buffer.back_mut()
    }

    /// Prepends `value` to the deque.
    /// If the deque `is_full` the last item is discarded and returned
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use fixed_slice_deque::FixedSliceDeque;
    /// let mut deq = FixedSliceDeque::new(1);
    /// deq.push_front(1);
    /// let pop = deq.push_front(2);
    /// assert_eq!(pop, Some(1));
    /// assert_eq!(deq.front(), Some(&2));
    /// ```
    #[inline]
    pub fn push_front(&mut self, value: T) -> Option<T> {
        let ret = self.is_full().then(|| self.buffer.pop_back()).flatten();
        self.buffer.push_front(value);
        ret
    }

    /// Appends `value` to the deque.
    /// If the deque `is_full` the first item is discarded and returned
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use fixed_slice_deque::FixedSliceDeque;
    /// let mut deq = FixedSliceDeque::new(1);
    /// deq.push_back(1);
    /// let pop = deq.push_back(3);
    /// assert_eq!(pop, Some(1));
    /// assert_eq!(deq.back(), Some(&3));
    /// ```
    #[inline]
    pub fn push_back(&mut self, value: T) -> Option<T> {
        let ret = self.is_full().then(|| self.buffer.pop_front()).flatten();
        self.buffer.push_back(value);
        ret
    }

    /// Prepends `value` to the deque if the deque is `!is_full` (not full)
    /// otherwise an error with the passed value is returned.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use fixed_slice_deque::FixedSliceDeque;
    /// let mut deq = FixedSliceDeque::new(0);
    /// let res = deq.try_push_front(1);
    /// assert_eq!(res, Err(1));
    /// ```
    #[inline]
    pub fn try_push_front(&mut self, value: T) -> Result<(), T> {
        if self.is_full() {
            return Err(value);
        }
        self.push_front(value);
        Ok(())
    }

    /// Appends `value` to the deque if the deque is `!is_full` (not full)
    /// otherwise an error with the passed value is returned.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use fixed_slice_deque::FixedSliceDeque;
    /// let mut deq = FixedSliceDeque::new(0);
    /// let res = deq.try_push_back(1);
    /// assert_eq!(res, Err(1));
    /// ```
    #[inline]
    pub fn try_push_back(&mut self, value: T) -> Result<(), T> {
        if self.is_full() {
            return Err(value);
        }
        self.push_back(value);
        Ok(())
    }

    /// Removes the first element and returns it, or `None` if the deque is
    /// empty.
    ///
    /// # Examples
    ///
    /// ```
    /// # use fixed_slice_deque::FixedSliceDeque;
    /// let mut deq = FixedSliceDeque::new(2);
    /// assert_eq!(deq.pop_front(), None);
    ///
    /// deq.push_back(1);
    /// deq.push_back(2);
    ///
    /// assert_eq!(deq.pop_front(), Some(1));
    /// assert_eq!(deq.pop_front(), Some(2));
    /// assert_eq!(deq.pop_front(), None);
    /// ```
    #[inline]
    pub fn pop_front(&mut self) -> Option<T> {
        self.buffer.pop_front()
    }

    /// Removes the last element from the deque and returns it, or `None` if it
    /// is empty.
    ///
    /// # Examples
    ///
    /// ```
    /// # use fixed_slice_deque::FixedSliceDeque;
    /// let mut deq = FixedSliceDeque::new(2);
    /// assert_eq!(deq.pop_back(), None);
    ///
    /// deq.push_back(1);
    /// deq.push_back(3);
    ///
    /// assert_eq!(deq.pop_back(), Some(3));
    /// assert_eq!(deq.pop_back(), Some(1));
    /// assert_eq!(deq.pop_back(), None);
    /// ```
    #[inline]
    pub fn pop_back(&mut self) -> Option<T> {
        self.buffer.pop_back()
    }

    /// Shortens the deque by removing excess elements from the front.
    /// At most `capacity` is removed (`len.min(self.capacity)`)
    ///
    /// If `len` is greater than the FixedSliceDeque's all items will be removed
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use fixed_slice_deque::{FixedSliceDeque, fsdeq};
    /// # fn main() {
    /// let mut deq = fsdeq![5, 10, 15];
    /// assert_eq!(deq, [5, 10, 15]);
    /// deq.truncate_front(1);
    /// assert_eq!(deq, [15]);
    /// # }
    /// ```
    #[inline]
    pub fn truncate_front(&mut self, len: usize) {
        self.buffer.truncate_front(len.min(self.capacity));
    }

    /// Shortens the deque by removing excess elements from the back.
    /// At most `capacity` is removed (`len.min(self.capacity)`)
    ///
    /// If `len` is greater than the FixedSliceDeque's all items will be removed
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use fixed_slice_deque::{FixedSliceDeque, fsdeq};
    /// # fn main() {
    /// let mut deq = fsdeq![5, 10, 15];
    /// assert_eq!(deq, [5, 10, 15]);
    /// deq.truncate_back(1);
    /// assert_eq!(deq, [5]);
    /// # }
    /// ```
    #[inline]
    pub fn truncate_back(&mut self, len: usize) {
        self.buffer.truncate_back(len.min(self.capacity));
    }

    /// Removes all values from the deque.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use fixed_slice_deque::{FixedSliceDeque, fsdeq};
    /// # fn main() {
    /// let mut deq = fsdeq![1];
    /// assert!(!deq.is_empty());
    /// deq.clear();
    /// assert!(deq.is_empty());
    /// # }
    #[inline]
    pub fn clear(&mut self) {
        self.buffer.clear()
    }

    /// Creates a draining iterator that removes the specified range in the
    /// deque and yields the removed items.
    ///
    /// Note 1: The element range is removed even if the iterator is only
    /// partially consumed or not consumed at all.
    ///
    /// Note 2: It is unspecified how many elements are removed from the deque
    /// if the `Drain` value is leaked.
    ///
    /// # Panics
    ///
    /// Panics if the starting point is greater than the end point or if
    /// the end point is greater than the length of the deque.
    ///
    /// # Examples
    ///
    /// ```
    /// # use fixed_slice_deque::{FixedSliceDeque, fsdeq};
    /// # fn main() {
    /// let mut deq = fsdeq![1, 2, 3];
    /// let u: Vec<_> = deq.drain(1..).collect();
    /// assert_eq!(deq, &[1]);
    /// assert_eq!(u, &[2, 3]);
    ///
    /// // A full range clears the deque
    /// deq.drain(..);
    /// assert_eq!(deq, &[]);
    /// # }
    /// ```
    #[inline]
    pub fn drain<R>(&mut self, range: R) -> slice_deque::Drain<T>
    where
        R: std::ops::RangeBounds<usize>,
    {
        self.buffer.drain(range)
    }

    /// Extracts a the inner [`SliceDeque`] buffer, consuming the [`FixedSliceDeque`]
    #[inline]
    pub fn into_inner(self) -> SliceDeque<T> {
        self.buffer
    }

    /// Inserts an `element` at `index` within the deque, shifting all elements
    /// with indices greater than or equal to `index` towards the back, keeping the deque max capacity.
    /// If the deque `if_full` the back-most element is returned.
    ///
    /// Element at index 0 is the front of the queue.
    ///
    /// # Panics
    ///
    /// Panics if `index` is greater than deque's length
    ///
    /// # Examples
    ///
    /// ```
    /// # use fixed_slice_deque::{FixedSliceDeque, fsdeq};
    /// # fn main() {
    /// let mut deq = fsdeq!['a', 'b', 'c'];
    /// assert_eq!(deq, &['a', 'b', 'c']);
    ///
    /// let c = deq.insert(1, 'd');
    /// assert_eq!(deq, &['a', 'd', 'b']);
    /// assert_eq!(c, Some('c'));
    /// # }
    /// ```
    #[inline]
    pub fn insert(&mut self, index: usize, element: T) -> Option<T> {
        let is_full = self.is_full();
        if index == 0 && is_full {
            return Some(element);
        }
        let ret = is_full.then(|| self.pop_back()).flatten();
        self.buffer.insert(index, element);
        ret
    }

    /// Removes and returns the element at position `index` within the deque.
    ///
    /// # Panics
    ///
    /// Panics if `index` is out of bounds.
    ///
    /// # Examples
    ///
    /// ```
    /// # use fixed_slice_deque::{FixedSliceDeque, fsdeq};
    /// # fn main() {
    /// let mut deq = fsdeq![1, 2, 3, 4, 5];
    /// assert_eq!(deq.remove(1), 2);
    /// assert_eq!(deq, [1, 3, 4, 5]);
    /// # }
    /// ```
    #[inline]
    pub fn remove(&mut self, index: usize) -> T {
        self.buffer.remove(index)
    }

    /// Retains only the elements specified by the predicate.
    ///
    /// That is, remove all elements `e` such that `f(&e)` returns `false`.
    /// This method operates in place and preserves the order of the
    /// retained elements.
    ///
    /// # Examples
    ///
    /// ```
    /// # use fixed_slice_deque::{FixedSliceDeque, fsdeq};
    /// # fn main() {
    /// let mut deq = fsdeq![1, 2, 3, 4];
    /// deq.retain(|&x| x % 2 == 0);
    /// assert_eq!(deq, [2, 4]);
    /// # }
    /// ```
    #[inline]
    pub fn retain<F>(&mut self, f: F)
    where
        F: FnMut(&T) -> bool,
    {
        self.buffer.retain(f);
    }

    /// Removes all but the first of consecutive elements in the deque that
    /// resolve to the same key.
    ///
    /// If the deque is sorted, this removes all duplicates.
    ///
    /// # Examples
    ///
    /// ```
    /// # use fixed_slice_deque::{FixedSliceDeque, fsdeq};
    /// # fn main() {
    /// let mut deq = fsdeq![10, 20, 21, 30, 20];
    ///
    /// deq.dedup_by_key(|i| *i / 10);
    /// assert_eq!(deq, [10, 20, 30, 20]);
    /// # }
    /// ```
    #[inline]
    pub fn dedup_by_key<F, K>(&mut self, key: F)
    where
        F: FnMut(&mut T) -> K,
        K: PartialEq,
    {
        self.buffer.dedup_by_key(key);
    }

    /// Removes all but the first of consecutive elements in the deque
    /// satisfying a given equality relation.
    ///
    /// The `same_bucket` function is passed references to two elements from
    /// the deque, and returns `true` if the elements compare equal, or
    /// `false` if they do not. The elements are passed in opposite order
    /// from their order in the deque, so if `same_bucket(a, b)` returns
    /// `true`, `a` is removed.
    ///
    /// If the deque is sorted, this removes all duplicates.
    ///
    /// # Examples
    ///
    /// ```
    /// # use fixed_slice_deque::{FixedSliceDeque, fsdeq};
    /// # fn main() {
    /// let mut deq = fsdeq!["foo", "bar", "Bar", "baz", "bar"];
    ///
    /// deq.dedup_by(|a, b| a.eq_ignore_ascii_case(b));
    ///
    /// assert_eq!(deq, ["foo", "bar", "baz", "bar"]);
    /// # }
    /// ```
    #[inline]
    pub fn dedup_by<F>(&mut self, same_bucket: F)
    where
        F: FnMut(&mut T, &mut T) -> bool,
    {
        self.buffer.dedup_by(same_bucket);
    }

    /// Creates an iterator which uses a closure to determine if an element
    /// should be removed.
    ///
    /// If the closure returns `true`, then the element is removed and yielded.
    /// If the closure returns `false`, it will try again, and call the closure
    /// on the next element, seeing if it passes the test.
    ///
    /// Using this method is equivalent to the following code:
    ///
    /// ```
    /// # use fixed_slice_deque::{FixedSliceDeque, fsdeq};
    /// # fn main() {
    /// # let some_predicate = |x: &mut i32| { *x == 2 || *x == 3 || *x == 6
    /// # };
    /// let mut deq = FixedSliceDeque::new(0);
    /// deq.extend(1..7);
    /// let mut i = 0;
    /// while i != deq.len() {
    ///     if some_predicate(&mut deq[i]) {
    ///         let val = deq.remove(i);
    ///     // your code here
    ///     } else {
    ///         i += 1;
    ///     }
    /// }
    /// # let mut expected = fsdeq![1, 4, 5];
    /// # assert_eq!(deq, expected);
    /// # }
    /// ```
    ///
    /// But `drain_filter` is easier to use. `drain_filter` is also more
    /// efficient, because it can backshift the elements of the deque in
    /// bulk.
    ///
    /// Note that `drain_filter` also lets you mutate every element in the
    /// filter closure, regardless of whether you choose to keep or remove
    /// it.
    ///
    ///
    /// # Examples
    ///
    /// Splitting a deque into evens and odds, reusing the original allocation:
    ///
    /// ```
    /// # use fixed_slice_deque::{FixedSliceDeque, fsdeq};
    /// # fn main() {
    /// let mut numbers = fsdeq![1, 2, 3, 4, 5, 6, 8, 9, 11, 13, 14, 15];
    ///
    /// let evens = numbers
    ///     .drain_filter(|x| *x % 2 == 0)
    ///     .collect::<FixedSliceDeque<_>>();
    /// let odds = numbers;
    ///
    /// assert_eq!(fsdeq![2, 4, 6, 8, 14], evens);
    /// assert_eq!(evens.capacity(), 5);
    /// assert_eq!(odds, fsdeq![1, 3, 5, 9, 11, 13, 15]);
    /// assert_eq!(odds.capacity(), 12);
    /// # }
    /// ```
    #[inline]
    pub fn drain_filter<F>(&mut self, filter: F) -> slice_deque::DrainFilter<T, F>
    where
        F: FnMut(&mut T) -> bool,
    {
        self.buffer.drain_filter(filter)
    }
}

impl<T: PartialEq> FixedSliceDeque<T> {
    /// Removes consecutive repeated elements in the deque.
    ///
    /// If the deque is sorted, this removes all duplicates.
    ///
    /// # Examples
    ///
    /// ```
    /// # use fixed_slice_deque::{FixedSliceDeque, fsdeq};
    /// # fn main() {
    /// let mut deq = fsdeq![1, 2, 2, 3, 2];
    ///
    /// deq.dedup();
    /// assert_eq!(deq, [1, 2, 3, 2]);
    ///
    /// deq.sort();
    /// assert_eq!(deq, [1, 2, 2, 3]);
    ///
    /// deq.dedup();
    /// assert_eq!(deq, [1, 2, 3]);
    /// # }
    /// ```
    #[inline]
    pub fn dedup(&mut self) {
        self.buffer.dedup();
    }

    /// Removes the first instance of `item` from the deque if the item exists.
    ///
    /// # Examples
    ///
    /// ```
    /// # use fixed_slice_deque::{FixedSliceDeque, fsdeq};
    /// # fn main() {
    /// let mut deq = fsdeq![1, 2, 3, 1];
    ///
    /// deq.remove_item(&1);
    /// assert_eq!(deq, &[2, 3, 1]);
    /// deq.remove_item(&1);
    /// assert_eq!(deq, &[2, 3]);
    /// # }
    /// ```
    #[inline]
    pub fn remove_item(&mut self, item: &T) -> Option<T> {
        self.buffer.remove_item(item)
    }
}

impl<T: Clone> FixedSliceDeque<T> {
    /// Clones and appends all elements in a slice to the [`FixedSliceDeque`]
    /// Capacity is upgraded so elements can fit.
    /// Iterates over the slice `other`, clones each element, and then appends
    /// it to this `SliceDeque`. The `other` slice is traversed in-order.
    ///
    /// Note that this function is same as `extend` except that it is
    /// specialized to work with slices instead. If and when Rust gets
    /// specialization this function will likely be deprecated (but still
    /// available).
    ///
    /// # Examples
    ///
    /// ```
    /// # use fixed_slice_deque::FixedSliceDeque;
    /// let mut deq = FixedSliceDeque::new(1);
    /// assert_eq!(deq.capacity(), 1);
    /// deq.push_back(1);
    /// deq.extend_from_slice(&[2, 3, 4]);
    /// assert_eq!(deq, [1, 2, 3, 4]);
    /// assert_eq!(deq.capacity(), 4);
    /// ```
    #[inline]
    pub fn extend_from_slice(&mut self, other: &[T]) {
        self.capacity = self.len() + other.len();
        self.buffer.extend_from_slice(other);
    }

    /// Modifies the [`FixedSliceDeque`] in-place so that `capacity` is equal to
    /// `new_capacity`, either by removing excess elements or by appending clones of
    /// `value` to the back.
    ///
    /// # Examples
    ///
    /// ```
    /// # use fixed_slice_deque::{FixedSliceDeque, fsdeq};
    /// # fn main() {
    /// let mut deq = fsdeq![5, 10, 15];
    /// assert_eq!(deq, [5, 10, 15]);
    /// assert_eq!(deq.capacity(), 3);
    ///
    /// deq.resize(2, 0);
    /// assert_eq!(deq, [5, 10]);
    ///assert_eq!(deq.capacity(), 2);
    ///
    /// deq.resize(5, 20);
    /// assert_eq!(deq, [5, 10, 20, 20, 20]);
    /// assert_eq!(deq.capacity(), 5);
    /// # }
    /// ```
    #[inline]
    pub fn resize(&mut self, new_capacity: usize, value: T) {
        self.capacity = new_capacity;
        self.buffer.resize(new_capacity, value);
    }
}

impl<T: Default> FixedSliceDeque<T> {
    /// Resizes the [`FixedSliceDeque`] in-place so that `capacity` is equal to `new_capacity`.
    ///
    /// If `new_capacity` is greater than `capacity`, the [`FixedSliceDeque`] is extended by the
    /// difference, with each additional slot filled with `Default::default()`.
    /// If `new_capacity` is less than `len`, the `[`FixedSliceDeque`] is simply truncated.
    ///
    /// This method uses `Default` to create new values on every push. If
    /// you'd rather `Clone` a given value, use [`resize`].
    ///
    ///
    /// # Examples
    ///
    /// ```
    /// # use fixed_slice_deque::{FixedSliceDeque, fsdeq};
    /// # fn main() {
    /// let mut deq = fsdeq![1, 2, 3];
    /// deq.resize_default(5);
    /// assert_eq!(deq, [1, 2, 3, 0, 0]);
    /// assert_eq!(deq.capacity(), 5);
    ///
    /// deq.resize_default(2);
    /// assert_eq!(deq, [1, 2]);
    /// assert_eq!(deq.capacity(), 2);
    /// # }
    /// ```
    ///
    /// [`resize`]: #method.resize
    #[inline]
    pub fn resize_default(&mut self, new_capacity: usize) {
        self.capacity = new_capacity;
        self.buffer.resize_default(new_capacity);
    }
}

impl<T> Deref for FixedSliceDeque<T> {
    type Target = [T];

    fn deref(&self) -> &Self::Target {
        self.as_slice()
    }
}

impl<T> DerefMut for FixedSliceDeque<T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.buffer.as_mut_slice()
    }
}

impl<T> From<SliceDeque<T>> for FixedSliceDeque<T> {
    fn from(deque: SliceDeque<T>) -> Self {
        Self::from_slice_deque(deque)
    }
}

impl<'a, T: Clone> From<&'a [T]> for FixedSliceDeque<T> {
    fn from(slice: &'a [T]) -> Self {
        Self {
            capacity: slice.len(),
            buffer: SliceDeque::from(slice),
        }
    }
}

impl<'a, T: Clone> From<&'a mut [T]> for FixedSliceDeque<T> {
    fn from(slice: &'a mut [T]) -> Self {
        Self {
            capacity: slice.len(),
            buffer: SliceDeque::from(slice),
        }
    }
}

impl<T> IntoIterator for FixedSliceDeque<T> {
    type Item = T;
    type IntoIter = slice_deque::IntoIter<T>;

    fn into_iter(self) -> Self::IntoIter {
        self.buffer.into_iter()
    }
}

impl<'a, T> IntoIterator for &'a FixedSliceDeque<T> {
    type Item = &'a T;
    type IntoIter = slice::Iter<'a, T>;
    #[inline]
    fn into_iter(self) -> slice::Iter<'a, T> {
        self.iter()
    }
}

impl<'a, T> IntoIterator for &'a mut FixedSliceDeque<T> {
    type Item = &'a mut T;
    type IntoIter = slice::IterMut<'a, T>;
    #[inline]
    fn into_iter(self) -> slice::IterMut<'a, T> {
        self.iter_mut()
    }
}

impl<T> Extend<T> for FixedSliceDeque<T> {
    #[inline]
    fn extend<I: IntoIterator<Item = T>>(&mut self, iter: I) {
        self.buffer.extend(iter);
        self.capacity = self.buffer.len();
    }
}

impl<'a, T: 'a + Copy> Extend<&'a T> for FixedSliceDeque<T> {
    fn extend<I: IntoIterator<Item = &'a T>>(&mut self, iter: I) {
        self.buffer.extend(iter.into_iter());
        self.capacity = self.buffer.len();
    }
}

impl<T> std::iter::FromIterator<T> for FixedSliceDeque<T> {
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        Self::from_slice_deque(SliceDeque::from_iter(iter.into_iter()))
    }
}

macro_rules! __impl_slice_eq1 {
    ($Lhs:ty, $Rhs:ty) => {
        __impl_slice_eq1! { $Lhs, $Rhs, Sized }
    };
    ($Lhs:ty, $Rhs:ty, $Bound:ident) => {
        impl<'a, 'b, A: $Bound, B> PartialEq<$Rhs> for $Lhs
        where
            A: PartialEq<B>,
        {
            #[inline]
            fn eq(&self, other: &$Rhs) -> bool {
                self.buffer[..] == other[..]
            }
        }
    };
}

__impl_slice_eq1! { FixedSliceDeque<A>, FixedSliceDeque<B> }
__impl_slice_eq1! { FixedSliceDeque<A>, SliceDeque<B> }
__impl_slice_eq1! { FixedSliceDeque<A>, &'b [B] }
__impl_slice_eq1! { FixedSliceDeque<A>, &'b mut [B] }
__impl_slice_eq1! { FixedSliceDeque<A>, Vec<B> }

macro_rules! array_impls {
    ($($N: expr)+) => {
        $(
            // NOTE: some less important impls are omitted to reduce code bloat
            __impl_slice_eq1! { FixedSliceDeque<A>, [B; $N] }
            __impl_slice_eq1! { FixedSliceDeque<A>, &'b [B; $N] }
        )+
    }
}

array_impls! {
     0  1  2  3  4  5  6  7  8  9
    10 11 12 13 14 15 16 17 18 19
    20 21 22 23 24 25 26 27 28 29
    30 31 32
}

#[cfg(test)]
mod tests {
    use crate::FixedSliceDeque;
    use std::cell::RefCell;
    use std::collections::HashMap;
    use std::rc::Rc;

    const SIZES_TO_TEST: &[usize] = &[2, 4, 8, 16, 32, 64, 128];

    #[derive(Clone, Debug)]
    struct WithDrop {
        counter: Rc<RefCell<usize>>,
    }

    impl Drop for WithDrop {
        fn drop(&mut self) {
            *self.counter.borrow_mut() += 1;
        }
    }

    #[test]
    fn get() {
        let mut deq = FixedSliceDeque::new(3);
        deq.push_back(3);
        deq.push_back(4);
        deq.push_back(5);
        assert_eq!(deq.get(1), Some(&4));
    }

    #[test]
    fn get_mut() {
        let mut deq = FixedSliceDeque::new(3);
        deq.push_back(3);
        deq.push_back(4);
        deq.push_back(5);
        assert_eq!(deq.get(1), Some(&4));
        if let Some(elem) = deq.get_mut(1) {
            *elem = 7;
        }
        assert_eq!(deq[1], 7);
    }

    #[test]
    fn is_empty() {
        let mut deq = FixedSliceDeque::new(1);
        assert!(deq.is_empty());
        deq.push_back(4);
        assert!(!deq.is_empty());
        deq.pop_front();
        assert!(deq.is_empty());
    }

    #[test]
    fn push_pop_front() {
        for size in SIZES_TO_TEST.iter().copied() {
            let mut v: FixedSliceDeque<usize> = FixedSliceDeque::new(size);
            for i in 0..size {
                v.push_front(i);
                assert_eq!(v.len(), i + 1);
                assert_eq!(v.capacity(), size);
                for j in 0..v.len() {
                    assert_eq!(*v.get(v.len() - j - 1).unwrap(), j);
                }
            }
            assert_eq!(v.len(), size);
            for i in 0..size {
                assert_eq!(*v.get(i).unwrap(), size - i - 1);
            }
            for i in 0..size {
                assert_eq!(v.len(), size - i);
                assert_eq!(v.capacity(), size);
                v.pop_front();
                for j in 0..v.len() {
                    assert_eq!(*v.get(v.len() - j - 1).unwrap(), j);
                }
            }
            assert_eq!(v.len(), 0);
            assert_eq!(v.capacity(), size);
        }
    }

    #[test]
    fn try_push_front() {
        let mut deque = FixedSliceDeque::new(0);
        assert_eq!(deque.try_push_front(1), Err(1));
    }

    #[test]
    fn try_push_back() {
        let mut deque = FixedSliceDeque::new(0);
        assert_eq!(deque.try_push_back(1), Err(1));
    }

    #[test]
    fn front_back_mut() {
        let mut v = fsdeq![1];
        assert_eq!(v.front_mut(), Some(&mut 1));
        assert_eq!(v.back_mut(), Some(&mut 1));
    }

    #[test]
    fn mut_slice() {
        let mut v = fsdeq![1];
        assert_eq!(v.as_mut_slice(), &mut [1]);
    }

    #[test]
    fn push_pop_back() {
        for size in SIZES_TO_TEST.iter().copied() {
            let mut v: FixedSliceDeque<_> = (0..size).collect();
            for i in 0..size {
                assert_eq!(v.len(), size - i);
                assert_eq!(v.capacity(), size);
                v.pop_back();
                for j in 0..v.len() {
                    assert_eq!(*v.get(j).unwrap(), j);
                }
            }
            assert_eq!(v.len(), 0);
            assert_eq!(v.capacity(), size);
        }
    }

    #[test]
    fn keeps_capacity() {
        for size in SIZES_TO_TEST.iter().copied() {
            let mut v: FixedSliceDeque<_> = (0..size).collect();
            for i in 0..size {
                let first = v.push_back(i);
                assert!(v.is_full());
                assert_eq!(v.capacity(), size);
                assert!(first.is_some());
            }

            for i in 0..size {
                let last = v.push_front(i);
                assert!(v.is_full());
                assert_eq!(v.capacity(), size);
                assert!(last.is_some());
            }
        }
    }

    #[test]
    fn from_slice_deque() {
        let deque = slice_deque::sdeq![1, 2, 3];
        let v: FixedSliceDeque<_> = deque.clone().into();
        assert_eq!(&v, &deque);
        let v: FixedSliceDeque<_> = FixedSliceDeque::from_slice_deque(deque.clone());
        assert_eq!(&v, &deque);
    }

    #[test]
    fn from_slice() {
        let deque = [1, 2, 3];
        let v: FixedSliceDeque<_> = deque.clone().as_slice().into();
        assert_eq!(&v, &deque);
    }

    #[test]
    fn from_slice_mut() {
        let deque = [1, 2, 3];
        let v: FixedSliceDeque<_> = deque.clone().as_mut_slice().into();
        assert_eq!(&v, &deque);
    }

    #[test]
    fn clear() {
        for size in SIZES_TO_TEST.iter().copied() {
            let counter = Rc::new(RefCell::new(0));
            let val = WithDrop {
                counter: counter.clone(),
            };
            assert_eq!(*counter.borrow(), 0);
            let mut deque: FixedSliceDeque<_> = (0..size).map(|_| val.clone()).collect();
            assert_eq!(*counter.borrow(), 0);
            deque.clear();
            assert_eq!(*counter.borrow(), size);
            assert_eq!(deque.len(), 0);
        }
    }

    #[test]
    fn resize() {
        for size in SIZES_TO_TEST.iter().copied() {
            let mut v: FixedSliceDeque<_> = (0..size).collect();
            let v_ref: FixedSliceDeque<_> = (0..size / 2).collect();
            v.resize(size / 2, 0);
            assert_eq!(v.len(), size / 2);
            assert_eq!(v.capacity(), size / 2);
            assert_eq!(v.as_slice(), v_ref.as_slice());

            v.resize(size, 3);
            assert_eq!(v.len(), size);
            assert_eq!(v.capacity(), size);
            assert_eq!(v.as_slice().last(), Some(&3));

            v.resize(0, 3);
            assert_eq!(v.len(), 0);
            assert_eq!(v.capacity(), 0);

            v.resize(size, 3);
            let v_ref: FixedSliceDeque<_> = (0..size).map(|_| 3usize).collect();
            assert_eq!(v.len(), size);
            assert_eq!(v.capacity(), size);
            assert_eq!(v_ref.len(), size);
            assert_eq!(v.as_slice(), v_ref.as_slice());
        }
    }

    #[test]
    fn resize_default() {
        for size in SIZES_TO_TEST.iter().copied() {
            let mut v: FixedSliceDeque<_> = (0..size).collect();
            let v_ref: FixedSliceDeque<_> = (0..size / 2).collect();
            v.resize_default(size / 2);
            assert_eq!(v.len(), size / 2);
            assert_eq!(v.capacity(), size / 2);
            assert_eq!(v.as_slice(), v_ref.as_slice());

            v.resize_default(size);
            assert_eq!(v.len(), size);
            assert_eq!(v.capacity(), size);
            assert_eq!(v.as_slice().last(), Some(&0));

            v.resize_default(0);
            assert_eq!(v.len(), 0);
            assert_eq!(v.capacity(), 0);

            v.resize_default(size);
            let v_ref: FixedSliceDeque<_> = (0..size).map(|_| 0).collect();
            assert_eq!(v.len(), size);
            assert_eq!(v.capacity(), size);
            assert_eq!(v_ref.len(), size);
            assert_eq!(v.as_slice(), v_ref.as_slice());
        }
    }

    #[test]
    fn iter() {
        let mut deq = FixedSliceDeque::new(3);
        deq.push_back(5);
        deq.push_back(3);
        deq.push_back(4);
        let b: &[_] = &[&5, &3, &4];
        let c: Vec<&i32> = deq.iter().collect();
        assert_eq!(&c[..], b);
    }

    #[test]
    fn iter_mut() {
        let mut deq = FixedSliceDeque::new(3);
        deq.push_back(5);
        deq.push_back(3);
        deq.push_back(4);
        for num in deq.iter_mut() {
            *num = *num - 2;
        }
        let b: &[_] = &[&mut 3, &mut 1, &mut 2];
        assert_eq!(&deq.iter_mut().collect::<Vec<&mut i32>>()[..], b);
    }

    #[test]
    fn hash_map() {
        let mut hm: HashMap<FixedSliceDeque<u32>, u32> = HashMap::new();
        let mut a = FixedSliceDeque::new(2);
        a.push_back(1);
        a.push_back(2);
        hm.insert(a.clone(), 3);
        let b = FixedSliceDeque::new(0);
        assert_eq!(hm.get(&a), Some(&3));
        assert_eq!(hm.get(&b), None);
    }

    #[test]
    fn eq() {
        let mut a = FixedSliceDeque::new(3);
        a.push_back(1);
        a.push_back(2);
        a.push_back(3);
        assert!(a == a);
        assert!(!(a != a));
    }

    #[test]
    fn vec_extend() {
        let mut v = FixedSliceDeque::new(0);
        let mut w = FixedSliceDeque::new(3);

        v.extend(w.clone().iter().copied());
        assert_eq!(v, &[]);

        v.extend(0..3);

        for i in 0..3 {
            w.push_back(i);
        }

        assert_eq!(v, w);

        v.extend(3..10);
        for i in 3..10 {
            w.push_back(i);
        }

        assert_eq!(v[7..10], w[..3]);
    }

    #[test]
    fn vec_extend_zst() {
        // Zero sized types
        #[derive(PartialEq, Eq, Debug, Clone, Copy)]
        struct Foo;

        let mut a = FixedSliceDeque::new(0);
        let b = fsdeq![Foo, Foo];

        a.extend_from_slice(&b);
        assert_eq!(&a, &b);
        assert_eq!(a.capacity(), 2);
    }

    #[test]
    fn vec_extend_ref() {
        let mut v = FixedSliceDeque::new(2);
        for &i in &[1, 2] {
            v.push_back(i);
        }
        assert_eq!(v.capacity(), 2);
        v.extend(&[3, 4, 5]);
        assert_eq!(v.capacity(), 5);

        assert_eq!(v.len(), 5);
        assert_eq!(v, [1, 2, 3, 4, 5]);

        let mut w = FixedSliceDeque::new(2);
        for &i in &[6, 7] {
            w.push_back(i);
        }
        assert_eq!(v.capacity(), 5);
        v.extend(&w);
        assert_eq!(v.capacity(), 7);

        assert_eq!(v.len(), 7);
        assert_eq!(v, [1, 2, 3, 4, 5, 6, 7]);
    }

    #[test]
    fn vec_slice_from_mut() {
        let mut values = fsdeq![1, 2, 3, 4, 5];
        {
            let slice = &mut values[2..];
            assert_eq!(slice, [3, 4, 5]);
            for p in slice {
                *p += 2;
            }
        }
        assert_eq!(values.capacity(), 5);
        assert_eq!(values, [1, 2, 5, 6, 7]);
    }

    #[test]
    fn vec_slice_to_mut() {
        let mut values = fsdeq![1, 2, 3, 4, 5];
        {
            let slice = &mut values[..2];
            assert_eq!(slice, [1, 2]);
            for p in slice {
                *p += 1;
            }
        }

        assert_eq!(values.capacity(), 5);
        assert_eq!(values, [2, 3, 3, 4, 5]);
    }

    #[test]
    fn vec_split_at_mut() {
        let mut values = fsdeq![1, 2, 3, 4, 5];
        {
            let (left, right) = values.split_at_mut(2);
            {
                let left: &[_] = left;
                assert_eq!(&left[..left.len()], &[1, 2]);
            }
            for p in left {
                *p += 1;
            }

            {
                let right: &[_] = right;
                assert_eq!(&right[..right.len()], &[3, 4, 5]);
            }
            for p in right {
                *p += 2;
            }
        }

        assert_eq!(values.capacity(), 5);
        assert_eq!(values, [2, 3, 5, 6, 7]);
    }

    #[test]
    fn vec_clone() {
        let v: FixedSliceDeque<i32> = fsdeq![];
        let w = fsdeq![1, 2, 3];

        assert_eq!(v, v.clone());

        let z = w.clone();
        assert_eq!(w, z);
        // they should be disjoint in memory.
        assert_ne!(w.as_ptr(), z.as_ptr())
    }

    #[test]
    fn vec_retain() {
        let mut deq = fsdeq![1, 2, 3, 4];
        deq.retain(|&x| x % 2 == 0);
        assert_eq!(deq, [2, 4]);
    }

    #[test]
    fn vec_dedup() {
        fn case(a: FixedSliceDeque<i32>, b: FixedSliceDeque<i32>) {
            let mut v = a;
            v.dedup();
            assert_eq!(v, b);
        }
        case(fsdeq![], fsdeq![]);
        case(fsdeq![1], fsdeq![1]);
        case(fsdeq![1, 1], fsdeq![1]);
        case(fsdeq![1, 2, 3], fsdeq![1, 2, 3]);
        case(fsdeq![1, 1, 2, 3], fsdeq![1, 2, 3]);
        case(fsdeq![1, 2, 2, 3], fsdeq![1, 2, 3]);
        case(fsdeq![1, 2, 3, 3], fsdeq![1, 2, 3]);
        case(fsdeq![1, 1, 2, 2, 2, 3, 3], fsdeq![1, 2, 3]);
    }

    #[test]
    fn vec_dedup_by_key() {
        fn case(a: FixedSliceDeque<i32>, b: FixedSliceDeque<i32>) {
            let mut v = a;
            v.dedup_by_key(|i| *i / 10);
            assert_eq!(v, b);
        }
        case(fsdeq![], fsdeq![]);
        case(fsdeq![10], fsdeq![10]);
        case(fsdeq![10, 11], fsdeq![10]);
        case(fsdeq![10, 20, 30], fsdeq![10, 20, 30]);
        case(fsdeq![10, 11, 20, 30], fsdeq![10, 20, 30]);
        case(fsdeq![10, 20, 21, 30], fsdeq![10, 20, 30]);
        case(fsdeq![10, 20, 30, 31], fsdeq![10, 20, 30]);
        case(fsdeq![10, 11, 20, 21, 22, 30, 31], fsdeq![10, 20, 30]);
    }

    #[test]
    fn vec_dedup_by() {
        let mut deq = fsdeq!["foo", "bar", "Bar", "baz", "bar"];
        deq.dedup_by(|a, b| a.eq_ignore_ascii_case(b));

        assert_eq!(deq, ["foo", "bar", "baz", "bar"]);

        let mut deq: FixedSliceDeque<(&'static str, i32)> =
            fsdeq![("foo", 1), ("foo", 2), ("bar", 3), ("bar", 4), ("bar", 5)];
        deq.dedup_by(|a, b| {
            a.0 == b.0 && {
                b.1 += a.1;
                true
            }
        });

        assert_eq!(deq, [("foo", 3), ("bar", 12)]);
    }

    #[test]
    fn zero_sized_values() {
        let mut v = FixedSliceDeque::new(1);
        assert_eq!(v.len(), 0);
        v.push_back(());
        assert_eq!(v.len(), 1);
        v.push_back(());
        assert_eq!(v.len(), 1);
        assert_eq!(v.pop_back(), Some(()));
        assert_eq!(v.pop_back(), None);
        assert_eq!(v.pop_back(), None);
        assert_eq!(v.capacity(), 1);

        assert_eq!(v.iter().count(), 0);
        v.push_back(());
        assert_eq!(v.iter().count(), 1);
        v.push_back(());
        assert_eq!(v.iter().count(), 1);

        for &() in &v {}

        assert_eq!(v.iter_mut().count(), 1);
        v.push_back(());
        assert_eq!(v.iter_mut().count(), 1);
        v.push_back(());
        assert_eq!(v.iter_mut().count(), 1);

        for &mut () in &mut v {}
        v.clear();
        assert_eq!(v.iter_mut().count(), 0);
        assert_eq!(v.capacity(), 1);
    }

    #[test]
    fn vec_partition() {
        assert_eq!(
            fsdeq![].into_iter().partition(|x: &i32| *x < 4),
            (fsdeq![], fsdeq![])
        );
        assert_eq!(
            fsdeq![1, 2, 3].into_iter().partition(|x| *x < 4),
            (fsdeq![1, 2, 3], fsdeq![])
        );
        assert_eq!(
            fsdeq![1, 2, 3].into_iter().partition(|x| *x < 2),
            (fsdeq![1], fsdeq![2, 3])
        );
        assert_eq!(
            fsdeq![1, 2, 3].into_iter().partition(|x| *x < 0),
            (fsdeq![], fsdeq![1, 2, 3])
        );
    }

    #[test]
    fn vec_zip_unzip() {
        let z1 = fsdeq![(1, 4), (2, 5), (3, 6)];

        let (left, right): (FixedSliceDeque<_>, FixedSliceDeque<_>) = z1.iter().cloned().unzip();

        assert_eq!((1, 4), (left[0], right[0]));
        assert_eq!((2, 5), (left[1], right[1]));
        assert_eq!((3, 6), (left[2], right[2]));
    }

    #[test]
    fn vec_vec_truncate_drop() {
        static mut DROPS: u32 = 0;
        struct Elem(i32);
        impl Drop for Elem {
            fn drop(&mut self) {
                unsafe {
                    DROPS += 1;
                }
            }
        }

        let mut v = fsdeq![Elem(1), Elem(2), Elem(3), Elem(4), Elem(5)];
        assert_eq!(unsafe { DROPS }, 0);
        v.truncate_back(3);
        assert_eq!(unsafe { DROPS }, 2);
        v.truncate_back(0);
        assert_eq!(unsafe { DROPS }, 5);
    }

    #[test]
    fn vec_vec_truncate_front_drop() {
        static mut DROPS: u32 = 0;
        struct Elem(i32);
        impl Drop for Elem {
            fn drop(&mut self) {
                unsafe {
                    DROPS += 1;
                }
            }
        }

        let mut v = fsdeq![Elem(1), Elem(2), Elem(3), Elem(4), Elem(5)];
        assert_eq!(unsafe { DROPS }, 0);
        v.truncate_front(3);
        assert_eq!(unsafe { DROPS }, 2);
        v.truncate_front(0);
        assert_eq!(unsafe { DROPS }, 5);
    }

    #[test]
    #[should_panic]
    fn vec_vec_truncate_fail() {
        struct BadElem(i32);
        impl Drop for BadElem {
            fn drop(&mut self) {
                let BadElem(ref mut x) = *self;
                if *x == 0xbadbeef {
                    panic!("BadElem panic: 0xbadbeef")
                }
            }
        }

        let mut v = fsdeq![BadElem(1), BadElem(2), BadElem(0xbadbeef), BadElem(4)];
        v.truncate_back(0);
    }

    #[test]
    fn vec_index() {
        let deq = fsdeq![1, 2, 3];
        assert_eq!(deq[1], 2);
    }

    #[test]
    #[should_panic]
    fn vec_index_out_of_bounds() {
        let deq = fsdeq![1, 2, 3];
        let _ = deq[3];
    }

    #[test]
    #[should_panic]
    fn vec_slice_out_of_bounds_1() {
        let x = fsdeq![1, 2, 3, 4, 5];
        let _ = &x[!0..];
    }

    #[test]
    #[should_panic]
    fn vec_slice_out_of_bounds_2() {
        let x = fsdeq![1, 2, 3, 4, 5];
        let _ = &x[..6];
    }

    #[test]
    #[should_panic]
    fn vec_slice_out_of_bounds_3() {
        let x = fsdeq![1, 2, 3, 4, 5];
        let _ = &x[!0..4];
    }

    #[test]
    #[should_panic]
    fn vec_slice_out_of_bounds_4() {
        let x = fsdeq![1, 2, 3, 4, 5];
        let _ = &x[1..6];
    }

    #[test]
    #[should_panic]
    fn vec_slice_out_of_bounds_5() {
        let x = fsdeq![1, 2, 3, 4, 5];
        let _ = &x[3..2];
    }

    #[test]
    fn vec_move_items() {
        let deq = fsdeq![1, 2, 3];
        let mut deq2 = FixedSliceDeque::new(3);
        for i in deq {
            deq2.push_back(i);
        }
        assert_eq!(deq2, [1, 2, 3]);
    }

    #[test]
    fn vec_move_items_reverse() {
        let deq = fsdeq![1, 2, 3];
        let mut deq2 = FixedSliceDeque::new(3);
        for i in deq.into_iter().rev() {
            deq2.push_back(i);
        }
        assert_eq!(deq2, [3, 2, 1]);
    }

    #[test]
    fn vec_move_items_zero_sized() {
        let deq = fsdeq![(), (), ()];
        let mut deq2 = FixedSliceDeque::new(3);
        for i in deq {
            deq2.push_back(i);
        }
        assert_eq!(deq2, [(), (), ()]);
    }

    #[test]
    fn vec_drain_items() {
        let mut deq = fsdeq![1, 2, 3];
        let mut deq2 = FixedSliceDeque::new(3);
        for i in deq.drain(..) {
            deq2.push_back(i);
        }
        assert_eq!(deq, []);
        assert_eq!(deq2, [1, 2, 3]);
        assert_eq!(deq.capacity(), deq2.capacity());
    }

    #[test]
    fn vec_drain_items_reverse() {
        let mut deq = fsdeq![1, 2, 3];
        let mut deq2 = FixedSliceDeque::new(3);
        for i in deq.drain(..).rev() {
            deq2.push_back(i);
        }
        assert_eq!(deq, []);
        assert_eq!(deq2, [3, 2, 1]);
        assert_eq!(deq.capacity(), deq2.capacity());
    }

    #[test]
    fn vec_drain_items_zero_sized() {
        let mut deq = fsdeq![(), (), ()];
        let mut deq2 = FixedSliceDeque::new(3);
        for i in deq.drain(..) {
            deq2.push_back(i);
        }
        assert_eq!(deq, []);
        assert_eq!(deq2, [(), (), ()]);
        assert_eq!(deq.capacity(), deq2.capacity());
    }

    #[test]
    #[should_panic]
    fn vec_drain_out_of_bounds() {
        let mut v = fsdeq![1, 2, 3, 4, 5];
        v.drain(5..6);
    }

    #[test]
    fn vec_drain_range() {
        let mut v = fsdeq![1, 2, 3, 4, 5];
        for _ in v.drain(4..) {}
        assert_eq!(v, &[1, 2, 3, 4]);

        let mut v: FixedSliceDeque<_> = (1..6).map(|x| x.to_string()).collect();
        for _ in v.drain(1..4) {}
        assert_eq!(v, &[1.to_string(), 5.to_string()]);

        let mut v: FixedSliceDeque<_> = (1..6).map(|x| x.to_string()).collect();
        for _ in v.drain(1..4).rev() {}
        assert_eq!(v, &[1.to_string(), 5.to_string()]);
    }

    #[test]
    fn vec_drain_range_zst() {
        let mut v: FixedSliceDeque<_> = fsdeq![(); 5];
        for _ in v.drain(1..4).rev() {}
        assert_eq!(v, &[(), ()]);
    }

    #[test]
    fn vec_drain_inclusive_range() {
        let mut v = fsdeq!['a', 'b', 'c', 'd', 'e'];
        for _ in v.drain(1..=3) {}
        assert_eq!(v, &['a', 'e']);

        let mut v: FixedSliceDeque<_> = (0..=5).map(|x| x.to_string()).collect();
        for _ in v.drain(1..=5) {}
        assert_eq!(v, &["0".to_string()]);

        let mut v: FixedSliceDeque<String> = (0..=5).map(|x| x.to_string()).collect();
        for _ in v.drain(0..=5) {}
        assert_eq!(v, FixedSliceDeque::<String>::new(0));

        let mut v: FixedSliceDeque<_> = (0..=5).map(|x| x.to_string()).collect();
        for _ in v.drain(0..=3) {}
        assert_eq!(v, &["4".to_string(), "5".to_string()]);

        let mut v: FixedSliceDeque<_> = (0..=1).map(|x| x.to_string()).collect();
        for _ in v.drain(..=0) {}
        assert_eq!(v, &["1".to_string()]);
    }

    #[test]
    #[should_panic]
    fn vec_drain_inclusive_out_of_bounds() {
        let mut v = fsdeq![1, 2, 3, 4, 5];
        v.drain(5..=5);
    }

    #[test]
    fn vec_append() {
        let mut deq = fsdeq![1, 2, 3];
        let mut deq2 = fsdeq![4, 5, 6];
        deq.append(&mut deq2);
        assert_eq!(deq, [4, 5, 6]);
        assert_eq!(deq2, []);
    }

    #[test]
    fn vec_append_small() {
        let mut v = FixedSliceDeque::new(10);
        let mut deq = fsdeq![1, 2, 3];
        let mut deq2 = fsdeq![4, 5, 6];
        v.append(&mut deq);
        v.append(&mut deq2);
        assert_eq!(v, [1, 2, 3, 4, 5, 6]);
        assert_eq!(v.capacity(), 10);
        assert_eq!(deq, []);
        assert_eq!(deq2, []);
    }

    #[test]
    fn vec_into_iter_as_slice() {
        let deq = fsdeq!['a', 'b', 'c'];
        let mut into_iter = deq.into_iter();
        assert_eq!(into_iter.as_slice(), &['a', 'b', 'c']);
        let _ = into_iter.next().unwrap();
        assert_eq!(into_iter.as_slice(), &['b', 'c']);
        let _ = into_iter.next().unwrap();
        let _ = into_iter.next().unwrap();
        assert_eq!(into_iter.as_slice(), &[]);
    }

    #[test]
    fn vec_into_iter_as_mut_slice() {
        let deq = fsdeq!['a', 'b', 'c'];
        let mut into_iter = deq.into_iter();
        assert_eq!(into_iter.as_slice(), &['a', 'b', 'c']);
        into_iter.as_mut_slice()[0] = 'x';
        into_iter.as_mut_slice()[1] = 'y';
        assert_eq!(into_iter.next().unwrap(), 'x');
        assert_eq!(into_iter.as_slice(), &['y', 'c']);
    }

    #[test]
    fn vec_into_iter_debug() {
        let deq = fsdeq!['a', 'b', 'c'];
        let into_iter = deq.into_iter();
        let debug = format!("{:?}", into_iter);
        assert_eq!(debug, "IntoIter(['a', 'b', 'c'])");
    }

    #[test]
    fn vec_into_iter_count() {
        assert_eq!(fsdeq![1, 2, 3].into_iter().count(), 3);
    }

    #[test]
    fn vec_into_iter_clone() {
        fn iter_equal<I: Iterator<Item = i32>>(it: I, slice: &[i32]) {
            let v: FixedSliceDeque<i32> = it.collect();
            assert_eq!(&v[..], slice);
        }
        let deq = fsdeq![1, 2, 3];
        let mut it = deq.into_iter();
        let it_c = it.clone();
        iter_equal(it_c, &[1, 2, 3]);
        assert_eq!(it.next(), Some(1));
        let mut it = it.rev();
        iter_equal(it.clone(), &[3, 2]);
        assert_eq!(it.next(), Some(3));
        iter_equal(it.clone(), &[2]);
        assert_eq!(it.next(), Some(2));
        iter_equal(it.clone(), &[]);
        assert_eq!(it.next(), None);
    }

    #[test]
    fn into_inner() {
        let fdeque = fsdeq![1, 2, 3];
        let deque = slice_deque::sdeq![1, 2, 3];
        assert_eq!(fdeque.into_inner(), deque);
    }

    #[test]
    fn drain_filter_empty() {
        let mut deq: FixedSliceDeque<i32> = fsdeq![];

        {
            let mut iter = deq.drain_filter(|_| true);
            assert_eq!(iter.size_hint(), (0, Some(0)));
            assert_eq!(iter.next(), None);
            assert_eq!(iter.size_hint(), (0, Some(0)));
            assert_eq!(iter.next(), None);
            assert_eq!(iter.size_hint(), (0, Some(0)));
        }
        assert_eq!(deq.len(), 0);
        assert_eq!(deq, fsdeq![]);
    }

    #[test]
    fn drain_filter_zst() {
        let mut deq = fsdeq![(), (), (), (), ()];
        let initial_len = deq.len();
        let mut count = 0;
        {
            let mut iter = deq.drain_filter(|_| true);
            assert_eq!(iter.size_hint(), (0, Some(initial_len)));
            while let Some(_) = iter.next() {
                count += 1;
                assert_eq!(iter.size_hint(), (0, Some(initial_len - count)));
            }
            assert_eq!(iter.size_hint(), (0, Some(0)));
            assert_eq!(iter.next(), None);
            assert_eq!(iter.size_hint(), (0, Some(0)));
        }

        assert_eq!(count, initial_len);
        assert_eq!(deq.len(), 0);
        assert_eq!(deq, fsdeq![]);
    }

    #[test]
    fn drain_filter_false() {
        let mut deq = fsdeq![1, 2, 3, 4, 5, 6, 7, 8, 9, 10];

        let initial_len = deq.len();
        let mut count = 0;
        {
            let mut iter = deq.drain_filter(|_| false);
            assert_eq!(iter.size_hint(), (0, Some(initial_len)));
            for _ in iter.by_ref() {
                count += 1;
            }
            assert_eq!(iter.size_hint(), (0, Some(0)));
            assert_eq!(iter.next(), None);
            assert_eq!(iter.size_hint(), (0, Some(0)));
        }

        assert_eq!(count, 0);
        assert_eq!(deq.len(), initial_len);
        assert_eq!(deq, fsdeq![1, 2, 3, 4, 5, 6, 7, 8, 9, 10]);
    }

    #[test]
    fn drain_filter_true() {
        let mut deq = fsdeq![1, 2, 3, 4, 5, 6, 7, 8, 9, 10];

        let initial_len = deq.len();
        let mut count = 0;
        {
            let mut iter = deq.drain_filter(|_| true);
            assert_eq!(iter.size_hint(), (0, Some(initial_len)));
            while let Some(_) = iter.next() {
                count += 1;
                assert_eq!(iter.size_hint(), (0, Some(initial_len - count)));
            }
            assert_eq!(iter.size_hint(), (0, Some(0)));
            assert_eq!(iter.next(), None);
            assert_eq!(iter.size_hint(), (0, Some(0)));
        }

        assert_eq!(count, initial_len);
        assert_eq!(deq.len(), 0);
        assert_eq!(deq, fsdeq![]);
    }

    #[test]
    fn drain_filter_complex() {
        {
            //                [+xxx++++++xxxxx++++x+x++]
            let mut deq = fsdeq![
                1, 2, 4, 6, 7, 9, 11, 13, 15, 17, 18, 20, 22, 24, 26, 27, 29, 31, 33, 34, 35, 36,
                37, 39,
            ];

            let removed = deq
                .drain_filter(|x| *x % 2 == 0)
                .collect::<FixedSliceDeque<_>>();
            assert_eq!(removed.len(), 10);
            assert_eq!(removed, fsdeq![2, 4, 6, 18, 20, 22, 24, 26, 34, 36]);

            assert_eq!(deq.len(), 14);
            assert_eq!(
                deq,
                fsdeq![1, 7, 9, 11, 13, 15, 17, 27, 29, 31, 33, 35, 37, 39]
            );
        }

        {
            //                [xxx++++++xxxxx++++x+x++]
            let mut deq = fsdeq![
                2, 4, 6, 7, 9, 11, 13, 15, 17, 18, 20, 22, 24, 26, 27, 29, 31, 33, 34, 35, 36, 37,
                39,
            ];

            let removed = deq
                .drain_filter(|x| *x % 2 == 0)
                .collect::<FixedSliceDeque<_>>();
            assert_eq!(removed.len(), 10);
            assert_eq!(removed, fsdeq![2, 4, 6, 18, 20, 22, 24, 26, 34, 36]);

            assert_eq!(deq.len(), 13);
            assert_eq!(
                deq,
                fsdeq![7, 9, 11, 13, 15, 17, 27, 29, 31, 33, 35, 37, 39]
            );
        }

        {
            //                [xxx++++++xxxxx++++x+x]
            let mut deq = fsdeq![
                2, 4, 6, 7, 9, 11, 13, 15, 17, 18, 20, 22, 24, 26, 27, 29, 31, 33, 34, 35, 36,
            ];

            let removed = deq
                .drain_filter(|x| *x % 2 == 0)
                .collect::<FixedSliceDeque<_>>();
            assert_eq!(removed.len(), 10);
            assert_eq!(removed, fsdeq![2, 4, 6, 18, 20, 22, 24, 26, 34, 36]);

            assert_eq!(deq.len(), 11);
            assert_eq!(deq, fsdeq![7, 9, 11, 13, 15, 17, 27, 29, 31, 33, 35]);
        }

        {
            //                [xxxxxxxxxx+++++++++++]
            let mut deq =
                fsdeq![2, 4, 6, 8, 10, 12, 14, 16, 18, 20, 1, 3, 5, 7, 9, 11, 13, 15, 17, 19,];

            let removed = deq
                .drain_filter(|x| *x % 2 == 0)
                .collect::<FixedSliceDeque<_>>();
            assert_eq!(removed.len(), 10);
            assert_eq!(removed, fsdeq![2, 4, 6, 8, 10, 12, 14, 16, 18, 20]);

            assert_eq!(deq.len(), 10);
            assert_eq!(deq, fsdeq![1, 3, 5, 7, 9, 11, 13, 15, 17, 19]);
        }

        {
            //                [+++++++++++xxxxxxxxxx]
            let mut deq =
                fsdeq![1, 3, 5, 7, 9, 11, 13, 15, 17, 19, 2, 4, 6, 8, 10, 12, 14, 16, 18, 20,];

            let removed = deq
                .drain_filter(|x| *x % 2 == 0)
                .collect::<FixedSliceDeque<_>>();
            assert_eq!(removed.len(), 10);
            assert_eq!(removed, fsdeq![2, 4, 6, 8, 10, 12, 14, 16, 18, 20]);

            assert_eq!(deq.len(), 10);
            assert_eq!(deq, fsdeq![1, 3, 5, 7, 9, 11, 13, 15, 17, 19]);
        }
    }

    #[test]
    fn vecdeque_simple() {
        let mut d = FixedSliceDeque::new(3);
        assert_eq!(d.len(), 0);
        assert_eq!(d.capacity(), 3);
        d.push_front(17);
        d.push_front(42);
        d.push_back(137);
        assert_eq!(d.len(), 3);
        assert_eq!(d.capacity(), 3);
        d.push_back(137);
        assert_eq!(d.len(), 3);
        assert_eq!(*d.front().unwrap(), 17);
        assert_eq!(*d.back().unwrap(), 137);
        let mut i = d.pop_front();
        assert_eq!(i, Some(17));
        i = d.pop_back();
        assert_eq!(i, Some(137));
        i = d.pop_back();
        assert_eq!(i, Some(137));
        i = d.pop_back();
        assert_eq!(i, None);
        assert_eq!(d.len(), 0);
        assert_eq!(d.capacity(), 3);
        d.push_back(3);
        assert_eq!(d.len(), 1);
        d.push_front(2);
        assert_eq!(d.len(), 2);
        d.push_back(4);
        assert_eq!(d.len(), 3);
        d.push_front(1);
        assert_eq!(d.len(), 3);
        assert_eq!(d[0], 1);
        assert_eq!(d[1], 2);
        assert_eq!(d[2], 3);
    }

    #[test]
    fn vecdeque_push_front_grow() {
        let mut deq = FixedSliceDeque::new(66);
        for i in 0..66 {
            deq.push_front(i);
        }
        assert_eq!(deq.len(), 66);

        for i in 0..66 {
            assert_eq!(deq[i], 65 - i);
        }

        let mut deq = FixedSliceDeque::new(66);
        for i in 0..66 {
            deq.push_back(i);
        }

        for i in 0..66 {
            assert_eq!(deq[i], i);
        }
    }

    #[test]
    fn vecdeque_index() {
        let mut deq = FixedSliceDeque::new(4);
        for i in 1..4 {
            deq.push_front(i);
        }
        assert_eq!(deq[1], 2);
    }

    #[test]
    #[should_panic]
    fn vecdeque_index_out_of_bounds() {
        let mut deq = FixedSliceDeque::new(1);
        for i in 1..4 {
            deq.push_front(i);
        }
        deq[3];
    }

    #[test]
    fn vecdeque_with_capacity() {
        let mut d = FixedSliceDeque::new(0);
        d.push_back(1);
        assert_eq!(d.len(), 1);
        let mut d = FixedSliceDeque::new(50);
        d.push_back(1);
        assert_eq!(d.len(), 1);
    }

    #[test]
    fn vecdeque_with_capacity_non_power_two() {
        let mut d3 = FixedSliceDeque::new(3);
        d3.push_back(1);

        // X = None, | = lo
        // [|1, X, X]
        assert_eq!(d3.pop_front(), Some(1));
        // [X, |X, X]
        assert_eq!(d3.front(), None);

        // [X, |3, X]
        d3.push_back(3);
        // [X, |3, 6]
        d3.push_back(6);
        // [X, X, |6]
        assert_eq!(d3.pop_front(), Some(3));

        // Pushing the lo past half way point to trigger
        // the 'B' scenario for growth
        // [9, X, |6]
        d3.push_back(9);
        // [9, 12, |6]
        d3.push_back(12);

        d3.push_back(15);
        // There used to be a bug here about how the
        // SliceDeque made growth assumptions about the
        // underlying Vec which didn't hold and lead
        // to corruption.
        // (Vec grows to next power of two)
        // good- [9, 12, 15, X, X, X, X, |6]
        // bug-  [15, 12, X, X, X, |6, X, X]
        assert_eq!(d3.pop_front(), Some(9));

        // Which leads us to the following state which
        // would be a failure case.
        // bug-  [15, 12, X, X, X, X, |X, X]
        assert_eq!(d3.front(), Some(&12));
        assert_eq!(d3.capacity(), 3);
    }

    #[test]
    fn vecdeque_iter() {
        let mut d = FixedSliceDeque::new(10);
        assert_eq!(d.iter().next(), None);
        assert_eq!(d.iter().size_hint(), (0, Some(0)));

        for i in 0..5 {
            d.push_back(i);
        }
        {
            let b: &[_] = &[&0, &1, &2, &3, &4];
            assert_eq!(d.iter().collect::<Vec<_>>(), b);
        }

        for i in 6..9 {
            d.push_front(i);
        }
        {
            let b: &[_] = &[&8, &7, &6, &0, &1, &2, &3, &4];
            assert_eq!(d.iter().collect::<Vec<_>>(), b);
        }

        let mut it = d.iter();
        let mut len = d.len();
        loop {
            match it.next() {
                None => break,
                _ => {
                    len -= 1;
                    assert_eq!(it.size_hint(), (len, Some(len)))
                }
            }
        }
    }

    #[test]
    fn vecdeque_rev_iter() {
        let mut d = FixedSliceDeque::new(10);
        assert_eq!(d.iter().rev().next(), None);

        for i in 0..5 {
            d.push_back(i);
        }
        {
            let b: &[_] = &[&4, &3, &2, &1, &0];
            assert_eq!(d.iter().rev().collect::<Vec<_>>(), b);
        }

        for i in 6..9 {
            d.push_front(i);
        }
        let b: &[_] = &[&4, &3, &2, &1, &0, &6, &7, &8];
        assert_eq!(d.iter().rev().collect::<Vec<_>>(), b);
    }

    #[test]
    fn vecdeque_mut_rev_iter_wrap() {
        let mut d = FixedSliceDeque::new(3);
        assert!(d.iter_mut().rev().next().is_none());

        d.push_back(1);
        d.push_back(2);
        d.push_back(3);
        assert_eq!(d.pop_front(), Some(1));
        d.push_back(4);

        assert_eq!(
            d.iter_mut().rev().map(|x| *x).collect::<Vec<_>>(),
            vec![4, 3, 2]
        );
    }

    #[test]
    fn vecdeque_mut_iter() {
        let mut d = FixedSliceDeque::new(3);
        assert!(d.iter_mut().next().is_none());

        for i in 0..3 {
            d.push_front(i);
        }

        for (i, elt) in d.iter_mut().enumerate() {
            assert_eq!(*elt, 2 - i);
            *elt = i;
        }

        {
            let mut it = d.iter_mut();
            assert_eq!(*it.next().unwrap(), 0);
            assert_eq!(*it.next().unwrap(), 1);
            assert_eq!(*it.next().unwrap(), 2);
            assert!(it.next().is_none());
        }
    }

    #[test]
    fn vecdeque_mut_rev_iter() {
        let mut d = FixedSliceDeque::new(3);
        assert!(d.iter_mut().rev().next().is_none());

        for i in 0..3 {
            d.push_front(i);
        }

        for (i, elt) in d.iter_mut().rev().enumerate() {
            assert_eq!(*elt, i);
            *elt = i;
        }

        {
            let mut it = d.iter_mut().rev();
            assert_eq!(*it.next().unwrap(), 0);
            assert_eq!(*it.next().unwrap(), 1);
            assert_eq!(*it.next().unwrap(), 2);
            assert!(it.next().is_none());
        }
    }

    #[test]
    fn vecdeque_into_iter() {
        // Empty iter
        {
            let d: FixedSliceDeque<i32> = FixedSliceDeque::new(0);
            let mut iter = d.into_iter();

            assert_eq!(iter.size_hint(), (0, Some(0)));
            assert_eq!(iter.next(), None);
            assert_eq!(iter.size_hint(), (0, Some(0)));
        }

        // simple iter
        {
            let mut d = FixedSliceDeque::new(5);
            for i in 0..5 {
                d.push_back(i);
            }

            let b = vec![0, 1, 2, 3, 4];
            assert_eq!(d.into_iter().collect::<Vec<_>>(), b);
        }

        // wrapped iter
        {
            let mut d = FixedSliceDeque::new(10);
            for i in 0..5 {
                d.push_back(i);
            }
            for i in 6..9 {
                d.push_front(i);
            }

            let b = vec![8, 7, 6, 0, 1, 2, 3, 4];
            assert_eq!(d.into_iter().collect::<Vec<_>>(), b);
        }

        // partially used
        {
            let mut d = FixedSliceDeque::new(10);
            for i in 0..5 {
                d.push_back(i);
            }
            for i in 6..9 {
                d.push_front(i);
            }

            let mut it = d.into_iter();
            assert_eq!(it.size_hint(), (8, Some(8)));
            assert_eq!(it.next(), Some(8));
            assert_eq!(it.size_hint(), (7, Some(7)));
            assert_eq!(it.next_back(), Some(4));
            assert_eq!(it.size_hint(), (6, Some(6)));
            assert_eq!(it.next(), Some(7));
            assert_eq!(it.size_hint(), (5, Some(5)));
        }
    }

    #[test]
    fn vecdeque_drain() {
        // Empty iter
        {
            let mut d: FixedSliceDeque<i32> = FixedSliceDeque::new(0);

            {
                let mut iter = d.drain(..);

                assert_eq!(iter.size_hint(), (0, Some(0)));
                assert_eq!(iter.next(), None);
                assert_eq!(iter.size_hint(), (0, Some(0)));
            }

            assert!(d.is_empty());
        }

        // simple iter
        {
            let mut d = FixedSliceDeque::new(5);
            for i in 0..5 {
                d.push_back(i);
            }

            assert_eq!(d.drain(..).collect::<Vec<_>>(), [0, 1, 2, 3, 4]);
            assert!(d.is_empty());
        }

        // wrapped iter
        {
            let mut d = FixedSliceDeque::new(10);
            for i in 0..5 {
                d.push_back(i);
            }
            for i in 6..9 {
                d.push_front(i);
            }

            assert_eq!(d.drain(..).collect::<Vec<_>>(), [8, 7, 6, 0, 1, 2, 3, 4]);
            assert!(d.is_empty());
        }

        // partially used
        {
            let mut d: FixedSliceDeque<_> = FixedSliceDeque::new(10);
            for i in 0..5 {
                d.push_back(i);
            }
            for i in 6..9 {
                d.push_front(i);
            }

            {
                let mut it = d.drain(..);
                assert_eq!(it.size_hint(), (8, Some(8)));
                assert_eq!(it.next(), Some(8));
                assert_eq!(it.size_hint(), (7, Some(7)));
                assert_eq!(it.next_back(), Some(4));
                assert_eq!(it.size_hint(), (6, Some(6)));
                assert_eq!(it.next(), Some(7));
                assert_eq!(it.size_hint(), (5, Some(5)));
            }
            assert!(d.is_empty());
        }
    }
}
