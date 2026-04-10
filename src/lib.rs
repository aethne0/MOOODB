#![allow(dead_code)]

#![warn(clippy::pedantic)]
#![warn(clippy::perf)]
#![warn(unreachable_pub)]
#![warn(clippy::redundant_clone)]
#![warn(clippy::let_and_return)]
#![warn(clippy::needless_pub_self)]
#![allow(clippy::explicit_iter_loop)]
#![allow(clippy::too_many_arguments)]
#![allow(clippy::doc_markdown)]
#![allow(clippy::cast_possible_truncation)]
#![allow(clippy::struct_field_names)]

//! • ▌ ▄ ·.                   ·▄▄▄▄  ▄▄▄▄·
//! ·██ ▐███▪▪     ▪     ▪     ██▪ ██ ▐█ ▀█▪
//! ▐█ ▌▐▌▐█· ▄█▀▄  ▄█▀▄  ▄█▀▄ ▐█· ▐█▌▐█▀▀█▄
//! ██ ██▌▐█▌▐█▌.▐▌▐█▌.▐▌▐█▌.▐▌██. ██ ██▄▪▐█
//! ▀▀  █▪▀▀▀ ▀█▄▀▪ ▀█▄▀▪ ▀█▄▀▪▀▀▀▀▀• ·▀▀▀▀
//!
//! **MOOODB** is a relational database management system

pub(crate) mod storage;
pub(crate) mod sync;
