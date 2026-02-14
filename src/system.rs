pub(crate) struct MmapBox<T> {
    ptr: *mut T,
    size: usize,
}

impl<T, const N: usize> MmapBox<[T; N]> {
    pub(crate) fn new_array_with(mut f: impl FnMut() -> T) -> Self {
        let size = size_of::<[T; N]>();
        let ptr = alloc_huge(size) as *mut T;
        for i in 0..N {
            unsafe { std::ptr::write(ptr.add(i), f()) };
        }
        Self {
            ptr: ptr as *mut [T; N],
            size,
        }
    }

    pub(crate) fn new_array_default() -> Self
    where
        T: Default,
    {
        Self::new_array_with(T::default)
    }
}

impl<T> Drop for MmapBox<T> {
    fn drop(&mut self) {
        unsafe { libc::munmap(self.ptr as *mut _, self.size) };
    }
}

impl<T> std::ops::Deref for MmapBox<T> {
    type Target = T;
    fn deref(&self) -> &T {
        unsafe { &*self.ptr }
    }
}

impl<T> std::ops::DerefMut for MmapBox<T> {
    fn deref_mut(&mut self) -> &mut T {
        unsafe { &mut *self.ptr }
    }
}

unsafe impl<T: Send> Send for MmapBox<T> {}
unsafe impl<T: Sync> Sync for MmapBox<T> {}

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

    assert_ne!(
        ptr,
        libc::MAP_FAILED,
        "mmap failed: {}",
        std::io::Error::last_os_error()
    );

    // let mlock_result = libc::mlock(ptr, size);

    ptr as *mut u8
}
