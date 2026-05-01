use std::mem::MaybeUninit;
use std::ptr::addr_of_mut;

use crate::mooo_assert;

// -------------------------------------------------------------------------------------------------
// ·▄▄▄▪  ▐▄• ▄ ▄▄▄ .·▄▄▄▄       ▄▄▄· ▄▄▄  ▄▄▄   ▄▄▄·  ▄· ▄▌
// ▐▄▄·██  █▌█▌▪▀▄.▀·██▪ ██     ▐█ ▀█ ▀▄ █·▀▄ █·▐█ ▀█ ▐█▪██▌
// ██▪ ▐█· ·██· ▐▀▀▪▄▐█· ▐█▌    ▄█▀▀█ ▐▀▀▄ ▐▀▀▄ ▄█▀▀█ ▐█▌▐█▪
// ██▌.▐█▌▪▐█·█▌▐█▄▄▌██. ██     ▐█ ▪▐▌▐█•█▌▐█•█▌▐█ ▪▐▌ ▐█▀·.    Fixed array & stack
// ▀▀▀ ▀▀▀•▀▀ ▀▀ ▀▀▀ ▀▀▀▀▀•      ▀  ▀ .▀  ▀.▀  ▀ ▀  ▀   ▀ •
// -------------------------------------------------------------------------------------------------

pub(crate) struct FixedArray<T, const LENGTH: usize> {
    head: usize,
    arr:  [MaybeUninit<T>; LENGTH],
}

impl<T, const LENGTH: usize> FixedArray<T, LENGTH> {
    pub(crate) const fn new() -> Self {
        Self { arr: [const { MaybeUninit::uninit() }; LENGTH], head: 0 }
    }

    pub(crate) fn new_boxed() -> Box<Self> {
        unsafe {
            let mut b: Box<MaybeUninit<Self>> = Box::new_uninit();
            let ptr = b.as_mut_ptr();

            addr_of_mut!((*ptr).head).write(0);
            addr_of_mut!((*ptr).arr).write([const { MaybeUninit::uninit() }; LENGTH]);

            b.assume_init()
        }
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

    /// not bounds checked - will panic
    pub(crate) const fn first_ref(&self) -> &T {
        mooo_assert!(self.head > 0);
        unsafe { self.arr[0].assume_init_ref() }
    }

    /// not bounds checked - will panic
    pub(crate) const fn first_mut(&mut self) -> &mut T {
        mooo_assert!(self.head > 0);
        unsafe { self.arr[0].assume_init_mut() }
    }

    /// not bounds checked - will panic
    pub(crate) const fn last_ref(&self) -> &T {
        mooo_assert!(self.head > 0);
        unsafe { self.arr[self.head - 1].assume_init_ref() }
    }

    /// not bounds checked - will panic
    pub(crate) const fn last_mut(&mut self) -> &mut T {
        mooo_assert!(self.head > 0);
        unsafe { self.arr[self.head - 1].assume_init_mut() }
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

    pub(crate) const fn pop_unchecked(&mut self) -> T {
        mooo_assert!(self.head > 0);
        self.head -= 1;
        unsafe { std::mem::replace(&mut self.arr[self.head], MaybeUninit::uninit()).assume_init() }
    }
}

impl<T, const LENGTH: usize> Drop for FixedArray<T, LENGTH> {
    fn drop(&mut self) {
        for i in 0..self.len() {
            unsafe { self.arr[i].assume_init_drop() };
        }
    }
}

impl<T: Clone, const L: usize> Clone for FixedArray<T, L> {
    fn clone(&self) -> Self {
        let mut cloned = Self::new();
        for i in 0..self.len() {
            cloned.push(self.index_ref(i).clone());
        }
        cloned
    }
}
