//! .▄▄ · ▄▄▄▄▄      ▄▄▄   ▄▄▄·  ▄▄ • ▄▄▄ .
//! ▐█ ▀. •██  ▪     ▀▄ █·▐█ ▀█ ▐█ ▀ ▪▀▄.▀·
//! ▄▀▀▀█▄ ▐█.▪ ▄█▀▄ ▐▀▀▄ ▄█▀▀█ ▄█ ▀█▄▐▀▀▪▄
//! ▐█▄▪▐█ ▐█▌·▐█▌.▐▌▐█•█▌▐█ ▪▐▌▐█▄▪▐█▐█▄▄▌
//!  ▀▀▀▀  ▀▀▀  ▀█▄▀▪.▀  ▀ ▀  ▀ ·▀▀▀▀  ▀▀▀
mod btree;
mod page_base;
mod page_btree;
mod page_superblock;
mod pager;

use pager::*;

const PAGE_SIZE: usize = 4096;
const PAGE_ID_NULL: u64 = u64::MAX;
