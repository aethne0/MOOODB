/// Fixed-size boxed-slice queue
pub(crate) struct Queue<T: Copy + Default> {
    buf: Box<[T]>,
    head: usize,
    len: usize,
}

impl<T: Copy + Default> Queue<T> {
    #[must_use]
    pub(crate) fn new(capacity: usize) -> Self {
        Queue { buf: vec![T::default(); capacity].into_boxed_slice(), head: 0, len: 0 }
    }

    pub(crate) fn len(&self) -> usize {
        self.len
    }

    pub(crate) fn push_back(&mut self, val: T) {
        assert!(self.len < self.buf.len(), "tried to push_back while FixedQueue already full");
        let tail = (self.head + self.len) % self.buf.len();
        self.buf[tail] = val;
        self.len += 1;
    }

    pub(crate) fn pop_front(&mut self) -> Option<T> {
        if self.len == 0 {
            return None;
        }
        let val = self.buf[self.head];
        self.head = (self.head + 1) % self.buf.len();
        self.len -= 1;
        Some(val)
    }
}
