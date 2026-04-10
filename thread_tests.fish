RUST_BACKTRACE=1 RUSTFLAGS="--cfg shuttle" cargo test shuttle --features shuttle
RUST_BACKTRACE=1 RUSTFLAGS="--cfg loom" cargo test loom --features loom
