// ▄▄▄▄▄▄▄▄ ..▄▄ · ▄▄▄▄▄.▄▄ ·
// •██  ▀▄.▀·▐█ ▀. •██  ▐█ ▀.
//  ▐█.▪▐▀▀▪▄▄▀▀▀█▄ ▐█.▪▄▀▀▀█▄
//  ▐█▌·▐█▄▄▌▐█▄▪▐█ ▐█▌·▐█▄▪▐█
//  ▀▀▀  ▀▀▀  ▀▀▀▀  ▀▀▀  ▀▀▀▀
use rand::rngs::ChaCha8Rng;
use rand::Rng;
use rand::RngExt;
use rand::SeedableRng;
use std::env::current_dir;
use std::fs::File;
use std::fs::OpenOptions;

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
fn deletoid_small() {
    eprintln!("");
    const SIZE: usize = 64 * 1024 * 1024;
    const FRAME_CNT: usize = SIZE / PAGE_SIZE;
    let mgr = Pager::new(FRAME_CNT, testfile()).unwrap();

    let mut rng = get_rand();

    const KEY_SIZE: usize = 22;
    const VAL_MASK: u64 = 0xffff_0000_0000_ffff;

    const INIT_CNT: usize = 20;
    const TX_CNT: usize = 1;
    const DELETES_PER_TX: usize = 20; // 13
    const _: () = mooo_assert!(INIT_CNT >= TX_CNT * DELETES_PER_TX);

    let dur = Durability::Flush;

    let mut entries = vec![];

    {
        let mut tx = mgr.write_tx();

        let mut btree = Btree::new(&mut tx).unwrap();

        for i in 1..=INIT_CNT {
            let mut key = [0u8; KEY_SIZE];
            rfill(&mut key, &mut rng);
            let val: u64 = rng.random::<u64>() | VAL_MASK;
            key[0..8].copy_from_slice(&(0x8000_0000_0000_0000 - i as u64).to_be_bytes());
            btree.insert(&mut tx, &key, &val.to_be_bytes()).unwrap();
            entries.push((key, val));
        }

        eprintln!("init");
        let mut crs = btree.cursor();
        while let Some(_) =
            crs.next(&tx, |k, v| eprintln!("{} {}", fmt_bytes(k), fmt_bytes(v))).unwrap()
        {}

        tx.set_catalog_root_pgid(btree.get_root_pgid());
        tx.commit(dur).unwrap();
    }

    entries.reverse();

    let start = std::time::Instant::now();
    for _ in 0..TX_CNT {
        let mut tx = mgr.write_tx();
        let _txid = tx.get_txid();
        let root_pgid = tx.get_catalog_root_pgid();
        if root_pgid == PGID_NULL {
            break;
        }
        let mut btree = Btree::from_pgid(root_pgid);

        for i in 0..DELETES_PER_TX {
            let (key, _) = entries.pop().unwrap();
            eprintln!("DELETE {}", fmt_bytes(&key));
            let x = btree.delete(&mut tx, &key).unwrap();
            if !x {
                eprintln!("ah{}", i);
            }
        }

        eprintln!("after");
        let mut crs = btree.cursor();
        while let Some(_) =
            crs.next(&tx, |k, v| eprintln!("{} {}", fmt_bytes(k), fmt_bytes(v))).unwrap()
        {}

        if btree.len(&tx).unwrap() != INIT_CNT - DELETES_PER_TX {
            eprintln!("big problem!");
        }

        tx.set_catalog_root_pgid(btree.get_root_pgid());
        tx.commit(dur).unwrap();
    }
    let end = std::time::Instant::now();

    eprintln!("{} deletes took {}s", TX_CNT, end.duration_since(start).as_secs_f32());
}

#[test]
fn cursoroid() {
    eprintln!("");
    const SIZE: usize = 64 * 1024 * 1024;
    const FRAME_CNT: usize = SIZE / PAGE_SIZE;
    let mgr = Pager::new(FRAME_CNT, testfile()).unwrap();

    let mut rng = get_rand();

    const KEY_SIZE: usize = 24;
    const VAL_MASK: u64 = 0xffff_0000_0000_ffff;

    const INIT_CNT: usize = 20;

    let dur = Durability::Flush;

    {
        let mut tx = mgr.write_tx();

        let mut btree = Btree::new(&mut tx).unwrap();

        for i in 1..=INIT_CNT {
            let mut key = [0u8; KEY_SIZE];
            rfill(&mut key, &mut rng);
            let val: u64 = rng.random::<u64>() | VAL_MASK;
            key[0..2].copy_from_slice(&(0xffff - i as u16).to_be_bytes());
            btree.insert(&mut tx, &key, &val.to_be_bytes()).unwrap();
        }

        tx.set_catalog_root_pgid(btree.get_root_pgid());
        tx.commit(dur).unwrap();
    }

    {
        let tx = mgr.read_tx();
        let mut cursor = Btree::from_pgid(tx.get_catalog_root_pgid()).cursor();

        while let Some(res) =
            cursor.next(&tx, |key, val| Whatever { key: key.to_vec(), val: val.to_vec() }).unwrap()
        {
            eprintln!("{} -> {}", fmt_bytes(&res.key), fmt_bytes(&res.val));
        }
    }
}

struct Whatever {
    key: Vec<u8>,
    val: Vec<u8>,
}

#[test]
fn deletoid_2() {
    eprintln!("");
    const SIZE: usize = 8 * 1024 * 1024 * 1024;
    const FRAME_CNT: usize = SIZE / PAGE_SIZE;
    let mgr = Pager::new(FRAME_CNT, testfile()).unwrap();

    let mut rng = get_rand();

    const KEY_SIZE: usize = 24;
    const VAL_MASK: u64 = 0xffff_0000_0000_ffff;

    const INIT_CNT: usize = 2_000_000;
    const TX_CNT: usize = 1_000_000;
    const DELETES_PER_TX: usize = 1;
    const _: () = mooo_assert!(INIT_CNT >= TX_CNT * DELETES_PER_TX);

    let dur = Durability::Flush;

    let mut entries = vec![];

    {
        let mut tx = mgr.write_tx();

        let mut btree = Btree::new(&mut tx).unwrap();

        for i in 1..=INIT_CNT {
            let mut key = [0u8; KEY_SIZE];
            rfill(&mut key, &mut rng);
            let val: u64 = rng.random::<u64>() | VAL_MASK;
            key[0..8].copy_from_slice(&(0x8000_0000_0000_0000 - i as u64).to_be_bytes());
            btree.insert(&mut tx, &key, &val.to_be_bytes()).unwrap();
            entries.push((key, val));
        }

        tx.set_catalog_root_pgid(btree.get_root_pgid());
        tx.commit(dur).unwrap();
    }

    entries.reverse();

    let start = std::time::Instant::now();
    for _ in 0..TX_CNT {
        let mut tx = mgr.write_tx();
        let _txid = tx.get_txid();
        let root_pgid = tx.get_catalog_root_pgid();
        if root_pgid == PGID_NULL {
            break;
        }
        let mut btree = Btree::from_pgid(root_pgid);

        for _ in 0..DELETES_PER_TX {
            let (key, _) = entries.pop().unwrap();
            btree.delete(&mut tx, &key).unwrap();
        }

        tx.set_catalog_root_pgid(btree.get_root_pgid());
        tx.commit(dur).unwrap();
    }
    let end = std::time::Instant::now();

    // ~46s 4096
    eprintln!("{} deletes took {}s", TX_CNT, end.duration_since(start).as_secs_f32());
}
