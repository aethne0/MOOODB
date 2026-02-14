pub(crate) struct FixedQueue<T: Copy + Default, const N: usize> {
    buf: [T; N],
    head: usize,
    len: usize,
}

impl<T: Copy + Default, const N: usize> FixedQueue<T, N> {
    #[must_use]
    pub(crate) fn new() -> Self {
        FixedQueue {
            buf: [T::default(); N],
            head: 0,
            len: 0,
        }
    }

    pub(crate) fn push_back(&mut self, val: T) {
        assert!(self.len < N, "tried to push_back while FixedQueue already full");
        let tail = (self.head + self.len) % N;
        self.buf[tail] = val;
        self.len += 1;
    }

    pub(crate) fn pop_front(&mut self) -> Option<T> {
        if self.len == 0 {
            return None;
        }
        let val = self.buf[self.head];
        self.head = (self.head + 1) % N;
        self.len -= 1;
        Some(val)
    }
}
