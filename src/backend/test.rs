// ▄▄▄▄▄▄▄▄ ..▄▄ · ▄▄▄▄▄.▄▄ ·
// •██  ▀▄.▀·▐█ ▀. •██  ▐█ ▀.
//  ▐█.▪▐▀▀▪▄▄▀▀▀█▄ ▐█.▪▄▀▀▀█▄
//  ▐█▌·▐█▄▄▌▐█▄▪▐█ ▐█▌·▐█▄▪▐█
//  ▀▀▀  ▀▀▀  ▀▀▀▀  ▀▀▀  ▀▀▀▀
use std::env::current_dir;
use std::fs::File;
use std::hint::black_box;
use std::os::unix::fs::OpenOptionsExt;
use std::time::Instant;

use rand::rngs::ChaCha8Rng;
use rand::Rng;
use rand::RngExt;
use rand::SeedableRng;

use super::btree::Btree;
use super::*;
use crate::util::fmt_bytes;
use crate::MiB;

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

fn rfill_raw(buf: &mut [u8], rng: &mut ChaCha8Rng) {
    rng.fill_bytes(buf);
}

fn testfile() -> File {
    let test_name = std::thread::current().name().unwrap_or("unknown").to_string();
    let mut path = current_dir().unwrap();
    path.push(".test_dbs");
    std::fs::create_dir_all(&path).unwrap();
    path.push(format!("{}.moo", test_name));
    let mut opts = std::fs::OpenOptions::new();
    opts.read(true)
        .create(true)
        .write(true)
        .truncate(true)
        .custom_flags(libc::O_DIRECT)
        .open(&path)
        .unwrap()
}

// ------------ Tests ------------------------------------------------------------------------------

#[test]
fn deletoid_small() {
    eprintln!("");
    const SIZE: usize = 16 * 1024 * 1024;
    const FRAME_CNT: usize = SIZE / PAGE_SIZE;
    let mgr = StorageManager::new(FRAME_CNT, testfile()).unwrap();

    let mut rng = get_rand();

    const KEY_SIZE: usize = 22;
    const VAL_MASK: u64 = 0xffff_0000_0000_ffff;

    const INIT_CNT: usize = 1_000;
    const TX_CNT: usize = 100;
    const DELETES_PER_TX: usize = 9;
    const _: () = mooo_assert!(INIT_CNT >= TX_CNT * DELETES_PER_TX);

    let dur = Durability::Flush;

    let mut entries = vec![];

    {
        let mut tx = mgr.write_tx();

        let mut btree = Btree::new(&mut tx).unwrap();

        for _i in 1..=INIT_CNT {
            let mut key = [0u8; KEY_SIZE];
            rfill(&mut key, &mut rng);
            let val: u64 = rng.random::<u64>() | VAL_MASK;
            // key[0..8].copy_from_slice(&(0x8000_0000_0000_0000 - i as u64).to_be_bytes());
            btree.insert(&mut tx, &key, &val.to_be_bytes()).unwrap();
            entries.push((key, val));
        }

        /*
        let mut crs = btree.cursor();
        while let Some(_) =
            crs.next(&tx, |k, v| eprintln!("{} {}", fmt_bytes(k), fmt_bytes(v))).unwrap()
        {}
        */

        let meta = btree.meta(&tx).unwrap();
        eprintln!(
            "len {} | pages {} | pages(leaf) {} | pages(inner) {} | bytes {}",
            meta.entry_cnt,
            meta.page_cnt_total,
            meta.page_cnt_leaf,
            meta.page_cnt_inner,
            meta.bytes
        );

        tx.set_catalog_root_pgid(btree.get_root_pgid());
        tx.commit(dur).unwrap();
    }

    entries.reverse();

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
            let _x = btree.delete(&mut tx, &key).unwrap();
        }

        tx.set_catalog_root_pgid(btree.get_root_pgid());
        tx.commit(dur).unwrap();

        /*
        let tx = mgr.read_tx();
        let fl = Btree::from_pgid(tx.freelistpgid());
        let mut crs = fl.cursor();
        eprintln!(">>> freelist <<<");
        while let Some(e) =
            crs.next(&tx, |a, b| Whatever { key: a.to_vec(), val: b.to_vec() }).unwrap()
        {
            eprintln!("    {:?}", e.key);
        }
        */
    }
}

#[test]
fn cursoroid() {
    eprintln!("");
    const SIZE: usize = 64 * 1024 * 1024;
    const FRAME_CNT: usize = SIZE / PAGE_SIZE;
    let mgr = StorageManager::new(FRAME_CNT, testfile()).unwrap();

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

// #[test]
fn deletoid_2() {
    eprintln!("");
    const SIZE: usize = 8 * 1024 * 1024 * 1024;
    const FRAME_CNT: usize = SIZE / PAGE_SIZE;
    let mgr = StorageManager::new(FRAME_CNT, testfile()).unwrap();

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

#[test]
fn insertoid() {
    const SIZE: usize = MiB!(4096);
    const FRAME_CNT: usize = SIZE / PAGE_SIZE;
    let mgr = StorageManager::new(FRAME_CNT, testfile()).unwrap();

    let mut rng = get_rand();

    const KEY_SIZE: usize = 128;
    const VAL_MASK: u64 = 0xffff_0000_0000_ffff;

    const TX_CNT: usize = 10_000;
    const INSERTS_PER_TX: usize = 100;
    const _CNT: usize = TX_CNT * INSERTS_PER_TX;

    let dur = Durability::Sync;

    {
        let mut tx = mgr.write_tx();
        let btree = Btree::new(&mut tx).unwrap();
        tx.set_catalog_root_pgid(btree.get_root_pgid());
        tx.commit(dur).unwrap();
    }

    let start = Instant::now();

    for i in 0..TX_CNT {
        let mut tx = mgr.write_tx();
        let mut btree = Btree::from_pgid(tx.get_catalog_root_pgid());

        for _i in 0..=INSERTS_PER_TX {
            let mut entry = [0u8; KEY_SIZE];
            rfill(&mut entry, &mut rng);
            btree.insert(&mut tx, &entry[0..KEY_SIZE / 2], &entry[KEY_SIZE / 2..]).unwrap();
        }

        /*
        let mut crs = btree.cursor();
        while let Some(_) =
            crs.next(&tx, |k, v| eprintln!("{} {}", fmt_bytes(k), fmt_bytes(v))).unwrap()
        {}
        */

        tx.set_catalog_root_pgid(btree.get_root_pgid());
        tx.commit(dur).unwrap();

        if i % 100 == 1 {
            let now = Instant::now();
            /*
            let meta = btree.meta(&tx).unwrap();
            eprintln!(
                "[{:04}] - [ len {} | pages {} | pages(leaf) {} | pages(inner) {} | bytes {} ] [ {:.2} / sec ]",
                i,
                meta.entry_cnt,
                meta.page_cnt_total,
                meta.page_cnt_leaf,
                meta.page_cnt_inner,
                fmt_size(meta.bytes as usize),
                meta.entry_cnt as f64 / now.duration_since(start).as_secs_f64(),
            );
            */
            eprintln!(
                "[{:04}] [ {:.2} transactions / sec ] [ {:.0} entries / sec ]",
                i,
                i as f64 / now.duration_since(start).as_secs_f64(),
                (i * INSERTS_PER_TX) as f64 / now.duration_since(start).as_secs_f64(),
            );
        }

        /*
        let tx = mgr.read_tx();
        let fl = Btree::from_pgid(tx.freelistpgid());
        let mut crs = fl.cursor();
        eprintln!(">>> freelist <<<");
        while let Some(e) =
            crs.next(&tx, |a, b| Whatever { key: a.to_vec(), val: b.to_vec() }).unwrap()
        {
            eprintln!("{:?}", e.key);
        }
        */
    }
}

#[test]
fn readbig() {
    eprintln!("");
    const SIZE: usize = 8 * 1024 * 1024 * 1024;
    const FRAME_CNT: usize = SIZE / PAGE_SIZE;

    let mut opts = std::fs::OpenOptions::new();
    let file = opts.read(true).custom_flags(libc::O_DIRECT).open("/xblk/test_dbs/big.moo").unwrap();

    let mgr = StorageManager::open(FRAME_CNT, file, false).unwrap();

    const THREADS: usize = 16;

    for threads_ in 0..=THREADS {
        let threads = threads_.max(1);

        let to_look = THREADS * 200000 / threads;
        let bar_1 = std::sync::Barrier::new(threads);

        let start = Instant::now();
        std::thread::scope(|s| {
            for _t in 0..threads {
                s.spawn(|| {
                    bar_1.wait();
                    let tx = mgr.read_tx();
                    let mut cursor = Btree::from_pgid(tx.get_catalog_root_pgid()).cursor();
                    let mut counter = to_look;

                    while let Some(res) = cursor
                        .next(&tx, |key, val| Whatever { key: key.to_vec(), val: val.to_vec() })
                        .unwrap()
                    {
                        black_box(&res);
                        counter -= 1;
                        if counter == 0 {
                            break;
                        }
                    }
                });
            }
        });

        let end = Instant::now();
        eprintln!(
            "{} reads in {:.03}s | {:.0} / sec | {} threads",
            threads * to_look,
            end.duration_since(start).as_secs_f64(),
            (threads * to_look) as f64 / end.duration_since(start).as_secs_f64(),
            threads,
        );
    }
}

#[test]
fn demooid() {
    const SIZE: usize = MiB!(256);
    const FRAME_CNT: usize = SIZE / PAGE_SIZE;
    let mgr = StorageManager::new(FRAME_CNT, testfile()).unwrap();

    let mut rng = get_rand();

    const TX_CNT: usize = 10_000;
    const INSERTS_PER_TX: usize = 100;
    const _CNT: usize = TX_CNT * INSERTS_PER_TX;

    let dur = Durability::Sync;

    {
        let mut tx = mgr.write_tx();

        let mut btree = Btree::new(&mut tx).unwrap();

        for _ in 0..10 {
            let mut key = [0u8; 6];
            let mut val = [0u8; 24];
            rfill(&mut key, &mut rng);

            rfill(&mut val, &mut rng);
            for char in val.iter_mut() {
                *char -= 32;
            }

            btree.insert(&mut tx, &key, &val).unwrap();
        }

        tx.set_catalog_root_pgid(btree.get_root_pgid());

        tx.commit(dur).unwrap();
    }

    let mut tx = mgr.write_tx();

    let mut btree = Btree::from_pgid(tx.get_catalog_root_pgid());

    for _ in 0..1 {
        let mut key = [0u8; 6];
        let mut val = [0u8; 24];
        rfill(&mut key, &mut rng);

        rfill(&mut val, &mut rng);
        for char in val.iter_mut() {
            *char -= 32;
        }

        btree.insert(&mut tx, &key, &val).unwrap();
    }

    tx.set_catalog_root_pgid(btree.get_root_pgid());

    tx.commit(dur).unwrap();
}
