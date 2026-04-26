// ▄▄▄▄▄▄▄▄ ..▄▄ · ▄▄▄▄▄.▄▄ ·
// •██  ▀▄.▀·▐█ ▀. •██  ▐█ ▀.
//  ▐█.▪▐▀▀▪▄▄▀▀▀█▄ ▐█.▪▄▀▀▀█▄
//  ▐█▌·▐█▄▄▌▐█▄▪▐█ ▐█▌·▐█▄▪▐█
//  ▀▀▀  ▀▀▀  ▀▀▀▀  ▀▀▀  ▀▀▀▀
use std::env::current_dir;
use std::fs::File;
use std::fs::OpenOptions;

use rand::rngs::ChaCha8Rng;
use rand::Rng;
use rand::RngExt;
use rand::SeedableRng;

use super::btree::Btree;
use super::heap::Heap;
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

// ------------ Tests ------------------------------------------------------------------------------

#[test]
fn freelist() {
    eprintln!("");
    let mgr = Pager::new(1024, testfile());

    let mut rng = get_rand();

    // const KEY_SIZE: usize = BTREE_KEY_MAX_LEN;
    const KEY_SIZE: usize = 24;
    const VAL_MASK: u64 = 0xffff_0000_0000_ffff;
    const TX_CNT: usize = 10;
    const INSERTS_PER_TX_INIT: usize = 3;
    const INSERTS_PER_TX: usize = 3;

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

#[test]
fn btree_inserts_single() {
    eprintln!("");
    let mgr = Pager::new(64, testfile());

    // const KEY_SIZE: usize = BTREE_KEY_MAX_LEN;
    const KEY_SIZE: usize = 24;
    const VAL_MASK: u64 = 0xffff_0000_0000_ffff;
    const TX_CNT: usize = 0;
    const INSERTS_PER_TX_INIT: usize = 8;
    const DELETES_PER_TX: usize = 1;

    {
        let mut w_tx = mgr.write_tx();
        let mut alloc = w_tx.freelist_allocator().unwrap();

        let mut heap = Heap::new(&mut alloc).unwrap();
        heap.insert(&mut alloc, b"PLACEHOLDER").unwrap();
        heap.insert(&mut alloc, b"first tx").unwrap();
        w_tx.set_catalog_root_pgid(heap.get_root_pgid());
        w_tx.commit(Durability::Flush).unwrap();
    }

    for _ in 0..2 {
        // tx=3 (init, 2, 3)
        let mut w_tx = mgr.write_tx();
        let root_pgid = w_tx.get_catalog_root_pgid();
        let mut alloc = w_tx.freelist_allocator().unwrap();

        let mut heap = Heap::new_from_pgid(root_pgid);
        heap.insert(&mut alloc, b"second tx").unwrap();
        w_tx.set_catalog_root_pgid(heap.get_root_pgid());
        w_tx.commit(Durability::Flush).unwrap();
    }
}
