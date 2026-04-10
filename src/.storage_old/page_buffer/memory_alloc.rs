/// Platform specific memory allocation for the page-buffer
/// Eventually ill make this work for non-linux (maybe)
pub(super) struct SlabBox<T: ?Sized> {
    ptr: *mut T,
    raw: *mut libc::c_void, // thin base pointer for munmap
    size: usize,
}

impl<T> SlabBox<[T]> {
    pub(super) fn new_slice_with(count: usize, mut f: impl FnMut() -> T) -> (Self, usize) {
        let size = size_of::<T>() * count;
        let raw = alloc_huge(size).cast::<libc::c_void>();
        let thin = raw.cast::<T>();
        for i in 0..count {
            unsafe { std::ptr::write(thin.add(i), f()) };
        }
        (Self { ptr: std::ptr::slice_from_raw_parts_mut(thin, count), raw, size }, size)
    }
}

impl SlabBox<[u8]> {
    /// Allocates a raw byte slab of `size` bytes via mmap. The memory is zero-initialized.
    pub(super) fn new_raw(size: usize) -> Self {
        let raw = alloc_huge(size).cast::<libc::c_void>();
        Self { ptr: std::ptr::slice_from_raw_parts_mut(raw.cast(), size), raw, size }
    }

    /// Returns the base mutable pointer to the allocation.
    pub(super) const fn as_ptr(&self) -> *mut u8 {
        self.raw.cast()
    }
}

impl<T: ?Sized> Drop for SlabBox<T> {
    fn drop(&mut self) {
        unsafe { libc::munmap(self.raw, self.size) };
    }
}

impl<T: ?Sized> std::ops::Deref for SlabBox<T> {
    type Target = T;
    fn deref(&self) -> &T {
        unsafe { &*self.ptr }
    }
}

impl<T: ?Sized> std::ops::DerefMut for SlabBox<T> {
    fn deref_mut(&mut self) -> &mut T {
        unsafe { &mut *self.ptr }
    }
}

unsafe impl<T: ?Sized + Send> Send for SlabBox<T> {}
unsafe impl<T: ?Sized + Sync> Sync for SlabBox<T> {}

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

    ptr.cast()
}
