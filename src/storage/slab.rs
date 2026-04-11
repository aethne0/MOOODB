/// Platform specific memory allocation for the page-buffer
/// Eventually ill make this work for non-linux (maybe)
pub(super) struct SlabBox {
    ptr: *mut [u8],         // fat slice pointer — carries the length for Deref
    raw: *mut libc::c_void, // thin base pointer for munmap
    size: usize,
}

unsafe impl Send for SlabBox {}
unsafe impl Sync for SlabBox {}

impl SlabBox {
    pub(super) fn new_raw(size: usize) -> Self {
        assert!(size > 0);
        let flags = libc::MAP_PRIVATE | libc::MAP_ANONYMOUS | libc::MAP_POPULATE;
        let ptr = unsafe {
            libc::mmap(std::ptr::null_mut(), size, libc::PROT_READ | libc::PROT_WRITE, flags, -1, 0)
        };

        if ptr == libc::MAP_FAILED {
            log::error!(
                "mmap allocation failed - stopping. Error: {}",
                std::io::Error::last_os_error()
            );
            std::process::abort();
        }

        let raw = ptr.cast::<libc::c_void>();
        Self { ptr: std::ptr::slice_from_raw_parts_mut(raw.cast(), size), raw, size }
    }

    pub(super) const fn as_ptr(&self) -> *mut u8 {
        self.raw.cast()
    }
}

impl Drop for SlabBox {
    fn drop(&mut self) {
        unsafe { libc::munmap(self.raw, self.size) };
    }
}

impl std::ops::Deref for SlabBox {
    type Target = [u8];
    fn deref(&self) -> &[u8] {
        unsafe { &*self.ptr }
    }
}

impl std::ops::DerefMut for SlabBox {
    fn deref_mut(&mut self) -> &mut [u8] {
        unsafe { &mut *self.ptr }
    }
}
