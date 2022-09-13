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

    #[inline]
    pub fn truncate_front(&mut self, len: usize) {
        self.buffer.truncate_front(len.min(self.capacity));
    }

    #[inline]
    pub fn truncate_back(&mut self, len: usize) {
        self.buffer.truncate_back(len.min(self.capacity));
    }

    #[inline]
    pub fn clear(&mut self) {
        self.buffer.clear()
    }

    #[inline]
    pub fn drain<R>(&mut self, range: R) -> slice_deque::Drain<T>
    where
        R: std::ops::RangeBounds<usize>,
    {
        self.buffer.drain(range)
    }

    #[inline]
    pub fn into_inner(self) -> SliceDeque<T> {
        self.buffer
    }

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

    #[inline]
    pub fn remove(&mut self, index: usize) -> T {
        self.buffer.remove(index)
    }

    #[inline]
    pub fn retain<F>(&mut self, f: F)
    where
        F: FnMut(&T) -> bool,
    {
        self.buffer.retain(f);
    }

    #[inline]
    pub fn dedup_by_key<F, K>(&mut self, key: F)
    where
        F: FnMut(&mut T) -> K,
        K: PartialEq,
    {
        self.buffer.dedup_by_key(key);
    }

    #[inline]
    pub fn dedup_by<F>(&mut self, same_bucket: F)
    where
        F: FnMut(&mut T, &mut T) -> bool,
    {
        self.buffer.dedup_by(same_bucket);
    }

    #[inline]
    pub fn drain_filter<F>(&mut self, filter: F) -> slice_deque::DrainFilter<T, F>
    where
        F: FnMut(&mut T) -> bool,
    {
        self.buffer.drain_filter(filter)
    }
}

impl<T: PartialEq> FixedSliceDeque<T> {
    #[inline]
    pub fn dedup(&mut self) {
        self.buffer.dedup();
    }

    #[inline]
    pub fn remove_item(&mut self, item: &T) -> Option<T> {
        self.buffer.remove_item(item)
    }
}

impl<T: Clone> FixedSliceDeque<T> {
    #[inline]
    pub fn extend_from_slice(&mut self, other: &[T]) {
        self.buffer.extend_from_slice(other);
        self.capacity = self.len() + other.len();
    }

    #[inline]
    pub fn resize(&mut self, new_len: usize, value: T) {
        self.capacity = new_len;
        self.buffer.resize(new_len, value);
    }
}

impl<T: Default> FixedSliceDeque<T> {
    #[inline]
    pub fn resize_default(&mut self, new_len: usize) {
        self.capacity = new_len;
        self.buffer.resize_default(new_len);
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
        self.buffer.extend(iter)
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
