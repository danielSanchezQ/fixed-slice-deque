use slice_deque::SliceDeque;
use std::ops::Deref;

pub struct FixedSliceDeque<T> {
    buffer: SliceDeque<T>,
    size: usize,
}

impl<T> FixedSliceDeque<T> {
    #[inline]
    pub fn new(size: usize) -> Self {
        Self {
            buffer: SliceDeque::with_capacity(size),
            size,
        }
    }

    pub fn from_slice_deque(deque: SliceDeque<T>) -> Self {
        Self {
            size: deque.len(),
            buffer: deque,
        }
    }

    #[inline]
    pub fn is_full(&self) -> bool {
        self.buffer.len() == self.size
    }

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
        self.buffer.retain(f)
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
}

impl<T> Deref for FixedSliceDeque<T> {
    type Target = [T];

    fn deref(&self) -> &Self::Target {
        self.as_slice()
    }
}

impl<T> From<SliceDeque<T>> for FixedSliceDeque<T> {
    fn from(deque: SliceDeque<T>) -> Self {
        Self::from_slice_deque(deque)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn is_full() {}
}
