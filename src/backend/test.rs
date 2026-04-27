// ▄▄▄▄▄▄▄▄ ..▄▄ · ▄▄▄▄▄.▄▄ ·
// •██  ▀▄.▀·▐█ ▀. •██  ▐█ ▀.
//  ▐█.▪▐▀▀▪▄▄▀▀▀█▄ ▐█.▪▄▀▀▀█▄
//  ▐█▌·▐█▄▄▌▐█▄▪▐█ ▐█▌·▐█▄▪▐█
//  ▀▀▀  ▀▀▀  ▀▀▀▀  ▀▀▀  ▀▀▀▀
use std::env::current_dir;
use std::fs::File;
use std::fs::OpenOptions;
use std::hint::black_box;
use std::sync::atomic::AtomicUsize;

use rand::rngs::ChaCha8Rng;
use rand::Rng;
use rand::RngExt;
use rand::SeedableRng;
use rustc_hash::FxHashMap;

use crate::backend::heap::Heap;

use super::btree::Btree;
use super::*;

fn fmt_bytes(bytes: &[u8]) -> String {
    let inner: Vec<String> = bytes.iter().map(|b| format!("{b:02x}")).collect();
    format!("[{}]", inner.join(" "))
}

fn f_opts() -> OpenOptions {
    let mut opts = std::fs::OpenOptions::new();
    opts.create(true).write(true).truncate(true).read(true);
    opts
}

fn get_rand() -> ChaCha8Rng {
    ChaCha8Rng::seed_from_u64(0x1eaf_1eaf_1eaf_1eaf)
}

fn rfill(buf: &mut [u8], rng: &mut ChaCha8Rng) {
    // 0x61 - 0x7a
    const RANGE: u8 = 0x7a - 0x61;
    rng.fill_bytes(buf);
    for b in buf.iter_mut() {
        *b = (*b % RANGE) + 0x61;
    }
}

fn testfile() -> File {
    let test_name = std::thread::current().name().unwrap_or("unknown").to_string();
    let mut path = current_dir().unwrap();
    path.push(".test_dbs");
    std::fs::create_dir_all(&path).unwrap();
    path.push(format!("{}.moo", test_name));
    eprintln!("{:?}", &path);
    std::fs::OpenOptions::new()
        .read(true)
        .truncate(true)
        .create(true)
        .write(true)
        .open(&path)
        .unwrap()
}

// ------------ Tests ------------------------------------------------------------------------------

#[test]
fn deletoid() {
    eprintln!("");
    const SIZE: usize = 64 * 1024 * 1024;
    const FRAME_CNT: usize = SIZE / PAGE_SIZE;
    let mgr = Pager::new(FRAME_CNT, testfile()).unwrap();

    let mut rng = get_rand();

    const KEY_SIZE: usize = 8;
    const VAL_MASK: u64 = 0xffff_0000_0000_ffff;

    const INIT_CNT: usize = 12;
    const TX_CNT: usize = 4;
    const DELETES_PER_TX: usize = 1;
    const _: () = mooo_assert!(INIT_CNT >= TX_CNT * DELETES_PER_TX);

    let dur = Durability::Flush;

    let mut entries = FxHashMap::default();

    {
        let mut tx = mgr.write_tx();

        let mut btree = Btree::new(&mut tx).unwrap();

        for _ in 0..INIT_CNT {
            let mut key = [0u8; KEY_SIZE];
            rfill(&mut key, &mut rng);
            let val: u64 = rng.random::<u64>() | VAL_MASK;
            btree.insert(&mut tx, &key, val).unwrap();
            entries.insert(key, val);
        }

        tx.set_catalog_root_pgid(btree.get_root_pgid());
        tx.commit(dur).unwrap();
    }

    let mut entries = entries.into_keys().collect::<Vec<_>>();

    for _ in 0..TX_CNT {
        let mut tx = mgr.write_tx();
        let root_pgid = tx.get_catalog_root_pgid();
        if root_pgid == PGID_NULL {
            break;
        }
        let mut btree = Btree::from_pgid(root_pgid);

        for _ in 0..DELETES_PER_TX {
            let entry = entries.remove(rng.random_range(0..entries.len()));
            btree.delete(&mut tx, &entry).unwrap();
        }

        tx.set_catalog_root_pgid(btree.get_root_pgid());
        tx.commit(dur).unwrap();
    }
}

// TODO use fxhash

/*
#[test]
fn freelist() {
    eprintln!("");
    const SIZE: usize = 64 * 1024 * 1024;
    const FRAME_CNT: usize = SIZE / PAGE_SIZE;
    let mgr = Pager::new(FRAME_CNT, testfile());

    let mut rng = get_rand();

    // const KEY_SIZE: usize = 2;
    const KEY_SIZE: usize = 8;
    const VAL_MASK: u64 = 0xffff_0000_0000_ffff;
    // not including initial
    const TX_CNT: usize = 1;
    const INSERTS_PER_TX_INIT: usize = 1;
    const INSERTS_PER_TX: usize = 1;

    let dur = Durability::Flush;

    {
        let mut w_tx = mgr.write_tx();

        let mut alloc = w_tx.freelist_allocator().unwrap();
        let mut btree = Btree::new(&mut alloc).unwrap();

        for _ in 0..INSERTS_PER_TX_INIT {
            let mut key = [0u8; KEY_SIZE];
            rfill(&mut key, &mut rng);
            let val: u64 = rng.random::<u64>() | VAL_MASK;
            btree.insert(&mut alloc, &key, val).unwrap();
        }

        w_tx.set_catalog_root_pgid(btree.get_root_pgid());
        w_tx.commit(dur).unwrap();
    }

    for _ in 0..TX_CNT {
        let mut w_tx = mgr.write_tx();
        let root_pgid = w_tx.get_catalog_root_pgid();
        let mut alloc = w_tx.freelist_allocator().unwrap();
        let mut btree = Btree::new_from_root_pgid(root_pgid);

        for _ in 0..INSERTS_PER_TX {
            let mut key = [0u8; KEY_SIZE];
            rfill(&mut key, &mut rng);
            let val: u64 = rng.random::<u64>() | VAL_MASK;
            btree.insert(&mut alloc, &key, val).unwrap();
        }

        w_tx.set_catalog_root_pgid(btree.get_root_pgid());
        w_tx.commit(dur).unwrap();
    }
}
*/

#[test]
fn megalist() {
    const QUICK: usize = 1000;
    eprintln!("");
    const SIZE: usize = 1024 * 1024 * 64;
    const FRAME_CNT: usize = SIZE / PAGE_SIZE;
    let mgr = Pager::new(FRAME_CNT, testfile()).unwrap();

    let mut rng = get_rand();

    // const KEY_SIZE: usize = 2;
    const KEY_SIZE: usize = 8;
    const VAL_MASK: u64 = 0xffff_0000_0000_ffff;
    const TX_CNT: usize = 500_000 / QUICK;
    const INSERTS_PER_TX_INIT: usize = 1;
    const INSERTS_PER_TX: usize = 1;

    let dur = Durability::Flush;

    const RD_CNT: usize = 20_000_000 / QUICK;
    const READER_THREADS: usize = 3;

    let done = AtomicUsize::new(READER_THREADS);
    std::thread::scope(|s| {
        s.spawn(|| {
            {
                let mut tx = mgr.write_tx();
                let mut btree = Btree::new(&mut tx).unwrap();

                for _ in 0..INSERTS_PER_TX_INIT {
                    let mut key = [0u8; KEY_SIZE];
                    rfill(&mut key, &mut rng);
                    let val: u64 = rng.random::<u64>() | VAL_MASK;
                    btree.insert(&mut tx, &key, val).unwrap();
                }

                tx.set_catalog_root_pgid(btree.get_root_pgid());
                tx.commit(dur).unwrap();
            }

            for _ in 0..TX_CNT {
                if READER_THREADS > 0 && done.load(std::sync::atomic::Ordering::Relaxed) == 0 {
                    break;
                }
                let mut tx = mgr.write_tx();
                let root_pgid = tx.get_catalog_root_pgid();
                let mut btree = Btree::from_pgid(root_pgid);

                for _ in 0..INSERTS_PER_TX {
                    let mut key = [0u8; KEY_SIZE];
                    rfill(&mut key, &mut rng);
                    let val: u64 = rng.random::<u64>() | VAL_MASK;
                    btree.insert(&mut tx, &key, val).unwrap();
                }

                tx.set_catalog_root_pgid(btree.get_root_pgid());
                tx.commit(dur).unwrap();
            }
        });

        for _ in 0..READER_THREADS {
            s.spawn(|| {
                let mut rng = get_rand();
                std::thread::sleep(std::time::Duration::from_millis(10));

                for _ in 0..RD_CNT {
                    let r_tx = mgr.read_tx();
                    let root_pgid = r_tx.get_catalog_root_pgid();
                    let btree = Btree::from_pgid(root_pgid);
                    let mut key = [0u8; KEY_SIZE];
                    rfill(&mut key, &mut rng);
                    black_box(btree.get(&r_tx, &key).unwrap());
                }

                done.fetch_sub(1, std::sync::atomic::Ordering::Relaxed);
            });
        }
    });
    eprintln!("{} reads", RD_CNT * READER_THREADS);
    eprintln!("{} writes ", INSERTS_PER_TX * TX_CNT);
}

#[test]
fn btree_inserts_single() {
    eprintln!("");
    let mgr = Pager::new(64, testfile()).unwrap();

    // const KEY_SIZE: usize = BTREE_KEY_MAX_LEN;
    const KEY_SIZE: usize = 24;
    const VAL_MASK: u64 = 0xffff_0000_0000_ffff;
    const TX_CNT: usize = 0;
    const INSERTS_PER_TX_INIT: usize = 8;
    const DELETES_PER_TX: usize = 1;

    {
        let mut tx = mgr.write_tx();

        let mut heap = Heap::new(&mut tx).unwrap();
        heap.insert(&mut tx, b"PLACEHOLDER").unwrap();
        heap.insert(&mut tx, b"first tx").unwrap();
        tx.set_catalog_root_pgid(heap.get_root_pgid());
        tx.commit(Durability::Flush).unwrap();
    }

    for _ in 0..2 {
        // tx=3 (init, 2, 3)
        let mut tx = mgr.write_tx();
        let root_pgid = tx.get_catalog_root_pgid();

        let mut heap = Heap::new_from_pgid(root_pgid);
        heap.insert(&mut tx, b"second tx").unwrap();
        tx.set_catalog_root_pgid(heap.get_root_pgid());
        tx.commit(Durability::Flush).unwrap();
    }
}
