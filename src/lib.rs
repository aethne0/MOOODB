#![allow(dead_code)]

//! • ▌ ▄ ·.                   ·▄▄▄▄  ▄▄▄▄·
//! ·██ ▐███▪▪     ▪     ▪     ██▪ ██ ▐█ ▀█▪
//! ▐█ ▌▐▌▐█· ▄█▀▄  ▄█▀▄  ▄█▀▄ ▐█· ▐█▌▐█▀▀█▄
//! ██ ██▌▐█▌▐█▌.▐▌▐█▌.▐▌▐█▌.▐▌██. ██ ██▄▪▐█
//! ▀▀  █▪▀▀▀ ▀█▄▀▪ ▀█▄▀▪ ▀█▄▀▪▀▀▀▀▀• ·▀▀▀▀
//!
//! **MOOODB** is a relational database management system

mod io;
// Layer 1: Page        | Sorted / Heap / Superblock pages
mod page;
// Layer 2: Storage     | PageManager + PageBuffer
mod storage;
// Layer 3: Indicies    | Access Methods (BTree, HeapFile, Hash)
mod index;
// Layer 4: Table       | Tables, schema, row codec, catalog

// Layer 5: Query       | SQL parse, plan, execute
