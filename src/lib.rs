//! • ▌ ▄ ·.                   ·▄▄▄▄  ▄▄▄▄·
//! ·██ ▐███▪▪     ▪     ▪     ██▪ ██ ▐█ ▀█▪
//! ▐█ ▌▐▌▐█· ▄█▀▄  ▄█▀▄  ▄█▀▄ ▐█· ▐█▌▐█▀▀█▄
//! ██ ██▌▐█▌▐█▌.▐▌▐█▌.▐▌▐█▌.▐▌██. ██ ██▄▪▐█
//! ▀▀  █▪▀▀▀ ▀█▄▀▪ ▀█▄▀▪ ▀█▄▀▪▀▀▀▀▀• ·▀▀▀▀
//!
//! **MOOODB** is a copy-on-write relational database management system.
//!
//! Copyright (c) 2026 aethne0 aka yarn aka the high monke monk
//!
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
// TODO
#![allow(dead_code)]

pub(crate) mod fixed_array;

pub mod assert;
pub mod backend;
