use std::fmt::Write;

use crate::page::PAGE_SIZE;

pub fn hexdump(buf: &[u8; PAGE_SIZE]) {
    println!();
    const CHUNK: usize = 32;
    for (i, chunk) in buf[..PAGE_SIZE].chunks(CHUNK).enumerate() {
        if i * CHUNK == 0x40 as usize {
            println!("*** end of header ***");
        }
        print!("{:04x}: ", i * CHUNK);
        for byte in chunk {
            print!("{:02x} ", byte);
        }
        print!(" | ");
        for &byte in chunk {
            if byte.is_ascii_graphic() || byte == b' ' {
                print!("{}", byte as char);
            } else {
                print!(".");
            }
        }
        println!();
    }
}

pub fn hexify(bytes: &[u8]) -> String {
    if bytes.is_empty() {
        return String::new();
    }
    let mut s = String::with_capacity(bytes.len() * 3);
    for (i, byte) in bytes.iter().enumerate() {
        if i > 0 {
            s.push(' ');
        }
        write!(s, "{:02x}", byte).unwrap();
    }
    s
}
