// ▄▄▄▄▄▄▄▄ ..▄▄ · ▄▄▄▄▄.▄▄ ·
// •██  ▀▄.▀·▐█ ▀. •██  ▐█ ▀.
//  ▐█.▪▐▀▀▪▄▄▀▀▀█▄ ▐█.▪▄▀▀▀█▄
//  ▐█▌·▐█▄▄▌▐█▄▪▐█ ▐█▌·▐█▄▪▐█
//  ▀▀▀  ▀▀▀  ▀▀▀▀  ▀▀▀  ▀▀▀▀
use std::sync::atomic::AtomicUsize;

use rand::fill;
use rand::random;

use super::btree::Btree;
use super::*;
use crate::sync;

#[test]
fn btree_inserts_single() {
    let file = std::fs::OpenOptions::new()
        .create(true)
        .write(true)
        .read(true)
        .open("/xblk/test/test.moo")
        .unwrap();
    let mgr = Pager::new(64, file);

    {
        let w_tx = mgr.write_tx();
        let mut btree = Btree::new(&w_tx).unwrap();

        for _ in 0..5 {
            let mut key = [0u8; 24];
            fill(&mut key);
            let mut val: u64 = random();
            val |= 0xff00_0000_0000_00ff;
            btree.insert(&w_tx, &key, val.into()).unwrap();
        }

        w_tx.update_catalog_root_id(btree.root_id());
        w_tx.commit(Durability::Flush).unwrap();
    }

    {
        let w_tx = mgr.write_tx();
        let mut btree = Btree::from_root_id(w_tx.get_catalog_root_id());

        for _ in 0..5 {
            let mut key = [0u8; 24];
            fill(&mut key);
            let mut val: u64 = random();
            val |= 0xff00_0000_0000_00ff;
            btree.insert(&w_tx, &key, val.into()).unwrap();
        }

        w_tx.update_catalog_root_id(btree.root_id());
        w_tx.commit(Durability::Flush).unwrap();
    }
}

#[test]
fn btree_inserts_threads() {
    let file = tempfile::tempfile().unwrap();
    let mgr = Pager::new(64, file);

    eprintln!("");
    static CTR: AtomicUsize = AtomicUsize::new(0);

    sync::thread::scope(|s| {
        for _ in 0..8 {
            s.spawn(|| {
                let id = CTR.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                let w_tx = mgr.write_tx();
                eprintln!("t{} -> 1", id);

                let mut btree = Btree::new(&w_tx).unwrap();
                let root_page_id = btree.root_id();
                eprintln!("t{} -> 1 root_page_id {}", id, root_page_id);
                btree.insert(&w_tx, b"asd", 0xab.into()).unwrap();
                btree.insert(&w_tx, b"zxc", 0xbc.into()).unwrap();
                btree.insert(&w_tx, b"rewt", 0xde.into()).unwrap();

                w_tx.commit(Durability::Flush).unwrap();

                let r_tx = mgr.read_tx();

                let res = btree.get(&r_tx, b"rewt").unwrap();
                assert!(res.is_some_and(|val| val.get() == 0xde));

                let w_tx = mgr.write_tx();
                eprintln!("t{} -> 2", id);

                let mut btree = Btree::from_root_id(root_page_id);
                btree.insert(&w_tx, b"xxx", 0x12.into()).unwrap();
                btree.insert(&w_tx, b"zxc", 0x55.into()).unwrap();
                btree.insert(&w_tx, b"rewz", 0x77.into()).unwrap();

                eprintln!("t{} -> 2 root_page_id {}", id, btree.root_id());

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

                let mut btree = Btree::from_root_id(id as u64 % 2 + 2);
                btree.insert(&w_tx, b"xxx", 0x13.into()).unwrap();
                btree.insert(&w_tx, b"zxc", 0x56.into()).unwrap();
                btree.insert(&w_tx, b"rewz", 0x88.into()).unwrap();

                w_tx.commit(Durability::Flush).unwrap();
            });
        }
    });
}
