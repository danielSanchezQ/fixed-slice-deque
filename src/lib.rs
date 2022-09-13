use slice_deque::SliceDeque;
use std::ops::{Deref, DerefMut};
use std::slice;

#[derive(Debug, Clone, Eq, Hash)]
pub struct FixedSliceDeque<T> {
    buffer: SliceDeque<T>,
    size: usize,
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
            size,
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
            size: deque.len(),
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
        self.buffer.len() == self.size
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

    #[inline]
    pub fn len(&self) -> usize {
        self.buffer.len()
    }

    #[inline]
    pub fn as_slice(&self) -> &[T] {
        self.buffer.as_slice()
    }

    #[inline]
    pub fn as_mut_slice(&mut self) -> &mut [T] {
        self.buffer.as_mut_slice()
    }

    #[inline]
    pub fn append(&mut self, other: &mut Self) {
        if other.len() + self.len() <= self.size {
            self.buffer.append(&mut other.buffer);
        } else {
            other
                .buffer
                .truncate_back(other.len() - (self.size - self.len()));
            self.buffer.append(&mut other.buffer);
        }
        other.buffer.clear();
    }

    #[inline]
    pub fn front(&self) -> Option<&T> {
        self.buffer.front()
    }

    #[inline]
    pub fn front_mut(&mut self) -> Option<&mut T> {
        self.buffer.front_mut()
    }

    #[inline]
    pub fn back(&self) -> Option<&T> {
        self.buffer.back()
    }

    #[inline]
    pub fn back_mut(&mut self) -> Option<&mut T> {
        self.buffer.back_mut()
    }

    #[inline]
    pub fn push_front(&mut self, value: T) -> Option<T> {
        let ret = self.is_full().then(|| self.buffer.pop_back()).flatten();
        self.buffer.push_front(value);
        ret
    }

    #[inline]
    pub fn push_back(&mut self, value: T) -> Option<T> {
        let ret = self.is_full().then(|| self.buffer.pop_front()).flatten();
        self.buffer.push_back(value);
        ret
    }

    #[inline]
    pub fn try_push_front(&mut self, value: T) -> Result<(), T> {
        if self.is_full() {
            return Err(value);
        }
        self.push_front(value);
        Ok(())
    }

    #[inline]
    pub fn try_push_back(&mut self, value: T) -> Result<(), T> {
        if self.is_full() {
            return Err(value);
        }
        self.push_back(value);
        Ok(())
    }

    #[inline]
    pub fn pop_front(&mut self) -> Option<T> {
        self.buffer.pop_front()
    }

    #[inline]
    pub fn pop_back(&mut self) -> Option<T> {
        self.buffer.pop_back()
    }

    #[inline]
    pub fn truncate_front(&mut self, len: usize) {
        self.buffer.truncate_front(len.min(self.size));
    }

    #[inline]
    pub fn truncate_back(&mut self, len: usize) {
        self.buffer.truncate_back(len.min(self.size));
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
        self.size = self.len() + other.len();
    }

    #[inline]
    pub fn resize(&mut self, new_len: usize, value: T) {
        self.size = new_len;
        self.buffer.resize(new_len, value);
    }
}

impl<T: Default> FixedSliceDeque<T> {
    #[inline]
    pub fn resize_default(&mut self, new_len: usize) {
        self.size = new_len;
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
            size: slice.len(),
            buffer: SliceDeque::from(slice),
        }
    }
}

impl<'a, T: Clone> From<&'a mut [T]> for FixedSliceDeque<T> {
    fn from(slice: &'a mut [T]) -> Self {
        Self {
            size: slice.len(),
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
    use super::*;

    #[test]
    fn is_full() {}
}
