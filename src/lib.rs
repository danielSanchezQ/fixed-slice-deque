use slice_deque::SliceDeque;
use std::ops::{Deref, DerefMut};
use std::slice;

#[derive(Debug, Clone, Eq, Hash)]
pub struct FixedSliceDeque<T> {
    buffer: SliceDeque<T>,
    capacity: usize,
}

/// Creates a [`FixedSliceDeque`] containing the arguments.
///
/// `fsdeq!` allows `SliceDeque`s to be defined with the same syntax as array
/// expressions. There are two forms of this macro:
///
/// - Create a [`SliceDeque`] containing a given list of elements:
///
/// ```
/// # #[macro_use] extern crate fixed_slice_deque;
/// # use fixed_slice_deque::FixedSliceDeque;
/// # fn main() {
/// let v: FixedSliceDeque<i32> = fsdeq![1, 2, 3];
/// assert_eq!(v[0], 1);
/// assert_eq!(v[1], 2);
/// assert_eq!(v[2], 3);
/// # }
/// ```
///
/// - Create a [`SliceDeque`] from a given element and size:
///
/// ```
/// # #[macro_use] extern crate fixed_slice_deque;
/// # use fixed_slice_deque::FixedSliceDeque;
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
/// example, `sdeq![Rc::new(1); 5]` will create a deque of five references
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

    #[test]
    fn is_full() {}
}
