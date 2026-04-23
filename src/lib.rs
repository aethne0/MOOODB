//! monke.ca
//! Copyright (c) 2026 yarn (high monke monk)
//! Enjoy your programming, God willing.
//!
//! THE TERMS HAVE BEEN ORDAINED AS FOLLOWS:
//!
//! ANY OR ALL USE OF THE CONTAINED CODE COULD PUT YOU AND YOUR FAMILY IN DANGER
//! THIS INCLUDES BUT IS CERTAINLY NOT LIMITED TO:
//! - COSMIC DANGER
//! - MORTAL DANGER
//! - SPIRITUAL DANGER
//! - LEGAL DANGER
//! - DANGER OF A PREVIOUSLY UNKNOWN KIND
//!
//! • ▌ ▄ ·.                   ·▄▄▄▄  ▄▄▄▄·
//! ·██ ▐███▪▪     ▪     ▪     ██▪ ██ ▐█ ▀█▪
//! ▐█ ▌▐▌▐█· ▄█▀▄  ▄█▀▄  ▄█▀▄ ▐█· ▐█▌▐█▀▀█▄
//! ██ ██▌▐█▌▐█▌.▐▌▐█▌.▐▌▐█▌.▐▌██. ██ ██▄▪▐█
//! ▀▀  █▪▀▀▀ ▀█▄▀▪ ▀█▄▀▪ ▀█▄▀▪▀▀▀▀▀• ·▀▀▀▀
//!
//! **MOOODB** is a copy-on-write relational database management system.

#![warn(unreachable_pub)]
#![warn(clippy::pedantic)]
#![warn(clippy::perf)]
#![warn(clippy::redundant_clone)]
#![warn(clippy::let_and_return)]
#![warn(clippy::needless_pub_self)]
#![allow(clippy::explicit_iter_loop)]
#![allow(clippy::too_many_arguments)]
#![allow(clippy::doc_markdown)]
#![allow(clippy::cast_possible_truncation)]
#![allow(clippy::struct_field_names)]
#![allow(dead_code)] // TODO

pub mod assert;
pub mod storage;
pub mod sync;

// TODO we need some way mark claimed pages as de-claimed, if we end up aborting something
// see: Btree::pop_min_lt
//
// TODO move pageid back to after checksum
//
// TODO the freelist always bumpallocates, so we are leaking 1 page per tx
// this is quite tricky - could we have two freelists, one for each superblock?
// and we use one but append to the other...
// The problem right now is that we cant do btree operations on the freelist while also
// using the freelist allocator, cause we get page conflicts
//
// i think we need to keep a cursor on the OLD freelist root, and use that cursor to traverse as we
// free pages and use them for the NEW freelist root - i think this should work, all the previous
// freelist pages will be readonly
//
// TODO btree has large stack allocations
//
// TODO lazy doesnt work (need to write out dirty frames before evicting)
//
// TODO at high numbers of TXs we get some frame conflict error when we have a
// smaller pager size (frame count)
