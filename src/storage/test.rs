// ▄▄▄▄▄▄▄▄ ..▄▄ · ▄▄▄▄▄.▄▄ ·
// •██  ▀▄.▀·▐█ ▀. •██  ▐█ ▀.
//  ▐█.▪▐▀▀▪▄▄▀▀▀█▄ ▐█.▪▄▀▀▀█▄
//  ▐█▌·▐█▄▄▌▐█▄▪▐█ ▐█▌·▐█▄▪▐█
//  ▀▀▀  ▀▀▀  ▀▀▀▀  ▀▀▀  ▀▀▀▀
use std::env::current_dir;
use std::fs::File;
use std::fs::OpenOptions;
use std::sync::atomic::AtomicUsize;

use rand::rngs::ChaCha8Rng;
use rand::Rng;
use rand::RngExt;
use rand::SeedableRng;

use super::btree::Btree;
use super::*;
use crate::storage::heap::Heap;
use crate::storage::manager::HeapPtr;
use crate::sync;

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
    ChaCha8Rng::seed_from_u64(0x000000000_b00b135)
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
    path.push(format!("moootest_{}.moo", test_name));
    eprintln!("{:?}", &path);
    std::fs::OpenOptions::new()
        .read(true)
        .truncate(true)
        .create(true)
        .write(true)
        .open(&path)
        .unwrap()
}

#[test]
fn btree_inserts_single() {
    eprintln!("");
    let mgr = Pager::new(64, testfile());

    let mut rng = get_rand();

    // const KEY_SIZE: usize = BTREE_KEY_MAX_LEN;
    const KEY_SIZE: usize = 24;
    const VAL_MASK: u64 = 0xffff_0000_0000_ffff;
    const TX_CNT: usize = 4;
    const INSERTS_PER_TX_INIT: usize = 32;
    const INSERTS_PER_TX: usize = 32;

    {
        let w_tx = mgr.write_tx();
        let mut btree = Btree::new(&w_tx).unwrap();

        for _ in 0..INSERTS_PER_TX_INIT {
            let mut key = [0u8; KEY_SIZE];
            rfill(&mut key, &mut rng);
            let val: u64 = rng.random::<u64>() | VAL_MASK;
            btree.insert(&w_tx, &key, val).unwrap();
        }

        w_tx.update_catalog_root_id(btree.get_root_pgid());
        w_tx.commit(Durability::Flush).unwrap();
    }

    for _ in 0..(TX_CNT - 1) {
        let w_tx = mgr.write_tx();
        let mut btree = Btree::new_from_root_pgid(w_tx.get_catalog_root_id());

        for _ in 0..INSERTS_PER_TX {
            let mut key = [0u8; KEY_SIZE];
            rfill(&mut key, &mut rng);
            let val: u64 = rng.random::<u64>() | VAL_MASK;
            btree.insert(&w_tx, &key, val).unwrap();
        }

        w_tx.update_catalog_root_id(btree.get_root_pgid());
        w_tx.commit(Durability::Flush).unwrap();
    }
}

#[test]
fn btree_deletes_single() {
    eprintln!("");
    let mgr = Pager::new(64, testfile());
    let mut rng = get_rand();

    // const KEY_SIZE: usize = BTREE_KEY_MAX_LEN;
    const KEY_SIZE: usize = 24;
    const VAL_MASK: u64 = 0xffff_0000_0000_ffff;
    const TX_CNT: usize = 1;
    const INSERTS_PER_TX_INIT: usize = 8;
    const DELETES_PER_TX: usize = 0;

    let mut keys = vec![];

    {
        let w_tx = mgr.write_tx();
        let mut btree = Btree::new(&w_tx).unwrap();

        for _ in 0..INSERTS_PER_TX_INIT {
            let mut key = [0u8; KEY_SIZE];
            rfill(&mut key, &mut rng);
            keys.push(key.clone());
            let val: u64 = rng.random::<u64>() | VAL_MASK;
            btree.insert(&w_tx, &key, val).unwrap();
        }

        btree.insert(&w_tx, b"somekeyasdfasdfasdfasdfa", HeapPtr::new(5, 3)).unwrap();
        let mut heap = Heap::new(&w_tx).unwrap();
        for _ in 0..10 {
            heap.insert(&w_tx, b"yooo haha...").unwrap();
        }

        w_tx.update_catalog_root_id(btree.get_root_pgid());
        w_tx.commit(Durability::Flush).unwrap();
    }

    {
        let w_tx = mgr.write_tx();
        let mut heap = Heap::new_from_pgid(5);
        heap.delete(&w_tx, 1).unwrap();
        heap.delete(&w_tx, 2).unwrap();
        heap.delete(&w_tx, 3).unwrap();
        heap.insert(&w_tx, b"YOOO HAHA...").unwrap();
        w_tx.commit(Durability::Flush).unwrap();
    }

    let r_tx = mgr.read_tx();
    let btree = Btree::new_from_root_pgid(r_tx.get_catalog_root_id());
    let res = btree.get_min(&r_tx).unwrap().unwrap();
    eprintln!("min: {:016x}", res.get());

    for _ in 0..TX_CNT {
        let w_tx = mgr.write_tx();
        let mut btree = Btree::new_from_root_pgid(w_tx.get_catalog_root_id());

        for _ in 0..DELETES_PER_TX {
            if keys.is_empty() {
                return;
            }
            let key_idx = rng.random_range(0..keys.len());
            let key = keys.remove(key_idx);
            eprintln!("deleting: {}", fmt_bytes(&key));
            btree.delete(&w_tx, &key).unwrap();
        }

        w_tx.update_catalog_root_id(btree.get_root_pgid());
        w_tx.commit(Durability::Flush).unwrap();
    }
}

#[test]
fn btree_inserts_threads() {
    eprintln!("");
    let file = testfile();
    let mgr = Pager::new(64, file);

    static CTR: AtomicUsize = AtomicUsize::new(0);

    sync::thread::scope(|s| {
        for _ in 0..8 {
            s.spawn(|| {
                let id = CTR.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                let w_tx = mgr.write_tx();
                eprintln!("t{} -> 1", id);

                let mut btree = Btree::new(&w_tx).unwrap();
                let root_page_id = btree.get_root_pgid();
                eprintln!("t{} -> 1 root_page_id {}", id, root_page_id);
                btree.insert(&w_tx, b"asd", 0xab).unwrap();
                btree.insert(&w_tx, b"zxc", 0xbc).unwrap();
                btree.insert(&w_tx, b"rewt", 0xde).unwrap();

                w_tx.commit(Durability::Flush).unwrap();

                let r_tx = mgr.read_tx();

                let res = btree.get(&r_tx, b"rewt").unwrap();
                assert!(res.is_some_and(|val| val.get() == 0xde));

                let w_tx = mgr.write_tx();
                eprintln!("t{} -> 2", id);

                let mut btree = Btree::new_from_root_pgid(root_page_id);
                btree.insert(&w_tx, b"xxx", 0x12).unwrap();
                btree.insert(&w_tx, b"zxc", 0x55).unwrap();
                btree.insert(&w_tx, b"rewz", 0x77).unwrap();

                eprintln!("t{} -> 2 root_page_id {}", id, btree.get_root_pgid());

                w_tx.commit(Durability::Flush).unwrap();
            });
        }
    });

    CTR.store(0, std::sync::atomic::Ordering::Relaxed);
    sync::thread::scope(|s| {
        for _ in 0..8 {
            s.spawn(|| {
                let id = CTR.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                let w_tx = mgr.write_tx();

                let mut btree = Btree::new_from_root_pgid(id as u64 % 2 + 2);
                btree.insert(&w_tx, b"xxx", 0x13).unwrap();
                btree.insert(&w_tx, b"zxc", 0x56).unwrap();
                btree.insert(&w_tx, b"rewz", 0x88).unwrap();

                w_tx.commit(Durability::Flush).unwrap();
            });
        }
    });
}
