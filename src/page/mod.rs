#![allow(dead_code)]

mod macros;

pub(crate) mod page;

pub(crate) const PAGE_SIZE: usize = 0x100;
pub(crate) const PAGE_HEADER_SIZE: usize = 0x40;
pub(crate) use page::Page;

#[cfg(debug_assertions)]
pub fn hex(buf: &[u8; PAGE_SIZE]) {
    // Only display the first 256 bytes for a 16x16 grid
    println!();
    for (i, chunk) in buf[..256].chunks(16).enumerate() {
        // Print address/row offset
        print!("{:04x}: ", i * 16);

        // Print hex values
        for byte in chunk {
            print!("{:02x} ", byte);
        }

        // Print ASCII representation
        print!(" | ");
        for &byte in chunk {
            if byte.is_ascii_graphic() || byte == b' ' {
                print!("{}", byte as char);
            } else {
                print!(".");
            }
        }
        println!();
    }
}

#[cfg(test)]
mod test {
    use std::collections::{HashMap, HashSet};

    use claims::{assert_lt, assert_none};
    use rand::{rngs::StdRng, RngExt, SeedableRng};

    use crate::page::{page::PageType, Page, PAGE_SIZE};

    #[test]
    fn test_page_insert_get() {
        let mut buffer = [0u8; PAGE_SIZE];
        let mut p = Page::new_with_buffer(&mut buffer, 2, PageType::Leaf, 1, 3);

        let key = [1, 2, 3, 4];
        let val = [5, 6, 7, 8];
        let res = p.insert(&key, &val);

        assert!(res);

        let got = p.get(&key);

        assert_eq!(got, Some(&val[..]));
    }

    #[test]
    fn test_page_churn() {
        let mut buffer = [0u8; PAGE_SIZE];
        let mut the_page = Page::new_with_buffer(&mut buffer, 2, PageType::Leaf, 1, 3);

        let mut rng = StdRng::seed_from_u64(0);

        let mut key = [0u8; 6];
        let mut val = [0u8; 6];

        for _ in 0..PAGE_SIZE {
            rng.fill(&mut key);
            rng.fill(&mut val);
            let res = the_page.insert(&key, &val);
            assert!(res, "Hmm... {}", the_page.len());
            the_page.delete(&key);
        }
    }

    #[test]
    fn test_page_delete() {
        let mut buffer = [0u8; PAGE_SIZE];
        let mut the_page = Page::new_with_buffer(&mut buffer, 2, PageType::Leaf, 1, 3);

        let mut rng = StdRng::seed_from_u64(0);

        let mut kvs = HashSet::new();

        let mut key = [0u8; 6];
        let mut val = [0u8; 6];

        loop {
            rng.fill(&mut key);
            rng.fill(&mut val);

            let res = the_page.insert(&key, &val);
            if !res {
                break;
            }

            kvs.insert(key.clone());
        }

        for k in &kvs {
            the_page.delete(k);
            let res = the_page.get(k);
            assert_none!(res);
        }

        assert_eq!(the_page.len(), 0);
    }

    #[test]
    fn test_page_insert_many() {
        let mut buffer = [0u8; PAGE_SIZE];
        let mut the_page = Page::new_with_buffer(&mut buffer, 2, PageType::Leaf, 1, 3);

        let mut rng = StdRng::seed_from_u64(0);

        let mut kvs = HashMap::new();

        let mut key = [0u8; 6];
        let mut val = [0u8; 6];

        loop {
            rng.fill(&mut key);
            rng.fill(&mut val);

            let res = the_page.insert(&key, &val);
            if !res {
                break;
            }

            kvs.insert(key.clone(), val.clone());
        }

        // make sure theyre sorted
        let mut prev = None;
        for (k, v) in the_page.iter() {
            assert_eq!(v, kvs.get(k).unwrap());
            if let Some(prev) = prev {
                assert_lt!(prev, k);
            }
            prev = Some(k);
        }

        assert_eq!(the_page.iter().count(), kvs.len());
    }
}
