// In memory for now
use std::{
    collections::{HashMap, HashSet},
    sync::{
        atomic::{AtomicU64, Ordering},
        Mutex,
    },
};

use crate::page::PAGE_SIZE;

const PAGE_CNT: usize = 256;

use std::ptr::NonNull;

pub(crate) struct Pager {
    _slab: Box<[u8]>, // The only big allocation
    frames: Box<[Frame]>,
    mapping: Mutex<Mapping>,
}

// TODO: Temporary
struct Mapping {
    page_map: HashMap<u64, usize>,
    // should be a ring buffer at the very least
    free_frames: HashSet<usize>,
}

impl Pager {
    pub(crate) fn new() -> Self {
        let mut slab = vec![0u8; PAGE_CNT * PAGE_SIZE].into_boxed_slice();
        let base_ptr = slab.as_mut_ptr();

        let frames = (0..PAGE_CNT)
            .map(|i| {
                let offset = i * PAGE_SIZE;
                Frame {
                    ptr: unsafe { NonNull::new_unchecked(base_ptr.add(offset)) },
                    pins: AtomicU64::new(0),
                }
            })
            .collect::<Box<[_]>>();

        Self {
            _slab: slab,
            frames,
            mapping: Mutex::new(Mapping {
                page_map: HashMap::with_capacity(PAGE_CNT),
                free_frames: HashSet::from_iter(0..PAGE_CNT),
            }),
        }
    }

    pub(crate) fn get_page(&self, page_id: u64) -> FrameRef<'_> {
        let mut mapping = self.mapping.lock().unwrap();

        let found = mapping.page_map.get(&page_id).cloned();

        let frame = match found {
            Some(frame_id) => {
                self.frames[frame_id].pins.fetch_add(1, Ordering::Relaxed);
                FrameRef {
                    frame: &self.frames[frame_id],
                    frame_id: frame_id,
                }
            }
            None => {
                let frame_id = *mapping.free_frames.iter().next().unwrap();
                let frame = &self.frames[frame_id];

                mapping.free_frames.remove(&frame_id);
                mapping.page_map.insert(page_id, frame_id);

                FrameRef { frame, frame_id }
            }
        };

        frame
    }
}

pub(crate) struct Frame {
    ptr: NonNull<u8>,
    pins: AtomicU64,
}

unsafe impl Send for Frame {}
unsafe impl Sync for Frame {}

impl Frame {
    // SAFETY: Pager must outlive the returned reference

    pub fn buffer_mut(&self) -> &mut [u8; PAGE_SIZE] {
        unsafe { &mut *self.ptr.as_ptr().cast::<[u8; PAGE_SIZE]>() }
    }

    pub fn buffer(&self) -> &[u8; PAGE_SIZE] {
        unsafe { &*self.ptr.as_ptr().cast::<[u8; PAGE_SIZE]>() }
    }
}

/// Wrapper for a ref to a [Frame]. Acquiring this increments a
/// pin counter and `Drop` decrements it.
pub(crate) struct FrameRef<'a> {
    frame: &'a Frame,
    frame_id: usize,
}

impl<'a> std::ops::Deref for FrameRef<'a> {
    type Target = &'a Frame;

    fn deref(&self) -> &Self::Target {
        &self.frame
    }
}

impl<'a> Drop for FrameRef<'a> {
    fn drop(&mut self) {
        self.pins.fetch_sub(1, Ordering::Relaxed);
    }
}

/// ▄▄▄▄▄▄▄▄ ..▄▄ · ▄▄▄▄▄.▄▄ ·
/// •██  ▀▄.▀·▐█ ▀. •██  ▐█ ▀.
///  ▐█.▪▐▀▀▪▄▄▀▀▀█▄ ▐█.▪▄▀▀▀█▄
///  ▐█▌·▐█▄▄▌▐█▄▪▐█ ▐█▌·▐█▄▪▐█
///  ▀▀▀  ▀▀▀  ▀▀▀▀  ▀▀▀  ▀▀▀▀
#[cfg(test)]
mod test {
    use std::{thread, time::Duration};

    use rand::{Rng, TryRng};

    use crate::{page, pager::Pager};

    #[test]
    fn test_pager() {
        const PAGE_ID: u64 = 64;
        let pager = Box::leak(Box::new(Pager::new()));

        {
            let frame = pager.get_page(64);
            let mut page = page::PageSorted::new_with_buffer(
                frame.buffer_mut(),
                PAGE_ID,
                page::PageType::Leaf,
                1,
                2,
            );

            let key = [0x56; 16];
            let val = [0xab; 16];
            page.insert(&key, &val);
        }

        thread::sleep(Duration::from_millis(100));

        for _ in 0..128 {
            thread::spawn(|| {
                let mut rng = rand::rng();
                let frame = pager.get_page(PAGE_ID);

                thread::sleep(Duration::from_millis(
                    rng.try_next_u64().unwrap() % 1000 + 50,
                ));

                let buffer = frame.buffer_mut(); // TODO; this is cooked needs internal mut and guard
                let mut page = page::PageSorted::from_buffer(buffer);

                let mut key = [0x56u8; 16];
                rng.fill_bytes(&mut key);
                page.insert(&key, &key); // data race

                println!("{}", page.len());
            });
        }

        thread::sleep(Duration::from_millis(1100));
    }
}
