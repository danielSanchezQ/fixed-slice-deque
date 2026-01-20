use crate::FixedSliceDeque;

/// An iterator that filters elements and removes them from the deque.
pub struct DrainFilter<'a, T, F>
where
    F: FnMut(&mut T) -> bool,
{
    pub(crate) deque: &'a mut FixedSliceDeque<T>,
    pub(crate) filter: F,
    pub(crate) old_len: usize,
    pub(crate) idx: usize,
    pub(crate) del: usize,
}

impl<'a, T, F> Iterator for DrainFilter<'a, T, F>
where
    F: FnMut(&mut T) -> bool,
{
    type Item = T;

    fn next(&mut self) -> Option<T> {
        while self.idx < self.old_len {
            let i = self.idx;
            self.idx += 1;
            let current_idx = i - self.del;
            if (self.filter)(&mut self.deque.buffer[current_idx]) {
                self.del += 1;
                return self.deque.buffer.remove(current_idx);
            }
        }
        None
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (0, Some(self.old_len - self.idx))
    }
}

impl<'a, T, F> Drop for DrainFilter<'a, T, F>
where
    F: FnMut(&mut T) -> bool,
{
    fn drop(&mut self) {
        while self.next().is_some() {}
    }
}
