#![allow(dead_code)]

//! • ▌ ▄ ·.                   ·▄▄▄▄  ▄▄▄▄·
//! ·██ ▐███▪▪     ▪     ▪     ██▪ ██ ▐█ ▀█▪
//! ▐█ ▌▐▌▐█· ▄█▀▄  ▄█▀▄  ▄█▀▄ ▐█· ▐█▌▐█▀▀█▄
//! ██ ██▌▐█▌▐█▌.▐▌▐█▌.▐▌▐█▌.▐▌██. ██ ██▄▪▐█
//! ▀▀  █▪▀▀▀ ▀█▄▀▪ ▀█▄▀▪ ▀█▄▀▪▀▀▀▀▀• ·▀▀▀▀
//!
//! **MOOODB** is a relational database management system

mod macros;

mod buffer;
mod page;
mod system;

#[cfg(test)]
mod test_util;
