//! Platform specific memory allocation for the page-buffer
pub(crate) struct MmapBox<T: ?Sized> {
    ptr: *mut T,
    raw: *mut libc::c_void, // thin base pointer for munmap
    size: usize,
}

// impl<T, const N: usize> MmapBox<[T; N]> {
//     pub(crate) fn new_array_with(mut f: impl FnMut() -> T) -> Self {
//         let size = size_of::<[T; N]>();
//         let raw = alloc_huge(size) as *mut libc::c_void;
//         let ptr = raw as *mut T;
//         for i in 0..N {
//             unsafe { std::ptr::write(ptr.add(i), f()) };
//         }
//         Self { ptr: ptr as *mut [T; N], raw, size }
//     }
//
//     pub(crate) fn new_array_default() -> Self
//     where
//         T: Default,
//     {
//         Self::new_array_with(T::default)
//     }
// }

impl<T> MmapBox<[T]> {
    pub(crate) fn new_slice_with(count: usize, mut f: impl FnMut() -> T) -> (Self, usize) {
        let size = size_of::<T>() * count;
        let raw = alloc_huge(size) as *mut libc::c_void;
        let thin = raw as *mut T;
        for i in 0..count {
            unsafe { std::ptr::write(thin.add(i), f()) };
        }
        (Self { ptr: std::ptr::slice_from_raw_parts_mut(thin, count), raw, size }, size)
    }
}

impl<T: ?Sized> Drop for MmapBox<T> {
    fn drop(&mut self) {
        unsafe { libc::munmap(self.raw, self.size) };
    }
}

impl<T: ?Sized> std::ops::Deref for MmapBox<T> {
    type Target = T;
    fn deref(&self) -> &T {
        unsafe { &*self.ptr }
    }
}

impl<T: ?Sized> std::ops::DerefMut for MmapBox<T> {
    fn deref_mut(&mut self) -> &mut T {
        unsafe { &mut *self.ptr }
    }
}

unsafe impl<T: ?Sized + Send> Send for MmapBox<T> {}
unsafe impl<T: ?Sized + Sync> Sync for MmapBox<T> {}

fn alloc_huge(size: usize) -> *mut u8 {
    assert_ne!(size, 0);

    let flags = libc::MAP_PRIVATE | libc::MAP_ANONYMOUS | libc::MAP_POPULATE;

    let ptr = unsafe {
        libc::mmap(
            std::ptr::null_mut(),
            size,
            libc::PROT_READ | libc::PROT_WRITE,
            flags, // | libc::MAP_HUGETLB | MAP_HUGE_2MB,
            -1,
            0,
        )
    };

    assert_ne!(ptr, libc::MAP_FAILED, "mmap failed: {}", std::io::Error::last_os_error());

    // let mlock_result = libc::mlock(ptr, size);

    ptr as *mut u8
}
