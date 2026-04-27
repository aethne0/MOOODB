use std::mem::MaybeUninit;

use crate::mooo_assert;

pub(crate) struct StackArray<T, const LENGTH: usize> {
    head: usize,
    arr:  [MaybeUninit<T>; LENGTH],
}

impl<T, const LENGTH: usize> StackArray<T, LENGTH> {
    pub(crate) const fn new() -> Self {
        Self { arr: [const { MaybeUninit::uninit() }; LENGTH], head: 0 }
    }

    pub(crate) const fn capacity(&self) -> usize {
        LENGTH
    }

    /// drops members
    pub(crate) fn clear(&mut self) {
        for i in 0..self.len() {
            unsafe { self.arr[i].assume_init_drop() };
        }
        self.head = 0;
    }

    /// not bounds checked - will panic
    pub(crate) const fn push(&mut self, item: T) {
        mooo_assert!(self.head < LENGTH);
        self.arr[self.head] = MaybeUninit::new(item);
        self.head += 1;
    }

    /// not bounds checked - will panic
    pub(crate) const fn index_ref(&self, index: usize) -> &T {
        mooo_assert!(index < self.head);
        unsafe { self.arr[index].assume_init_ref() }
    }

    /// not bounds checked - will panic
    pub(crate) const fn index_mut(&mut self, index: usize) -> &mut T {
        mooo_assert!(index < self.head);
        unsafe { self.arr[index].assume_init_mut() }
    }

    pub(crate) const fn len(&self) -> usize {
        self.head
    }

    pub(crate) const fn is_full(&self) -> bool {
        self.head == LENGTH
    }

    pub(crate) const fn is_empty(&self) -> bool {
        self.head == 0
    }

    pub(crate) const fn pop(&mut self) -> Option<T> {
        if self.head > 0 {
            self.head -= 1;
            Some(unsafe {
                std::mem::replace(&mut self.arr[self.head], MaybeUninit::uninit()).assume_init()
            })
        } else {
            None
        }
    }
}

impl<T, const LENGTH: usize> Drop for StackArray<T, LENGTH> {
    fn drop(&mut self) {
        for i in 0..self.len() {
            unsafe { self.arr[i].assume_init_drop() };
        }
    }
}
