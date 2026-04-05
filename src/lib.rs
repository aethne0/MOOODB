#![allow(dead_code)]

//! • ▌ ▄ ·.                   ·▄▄▄▄  ▄▄▄▄·
//! ·██ ▐███▪▪     ▪     ▪     ██▪ ██ ▐█ ▀█▪
//! ▐█ ▌▐▌▐█· ▄█▀▄  ▄█▀▄  ▄█▀▄ ▐█· ▐█▌▐█▀▀█▄
//! ██ ██▌▐█▌▐█▌.▐▌▐█▌.▐▌▐█▌.▐▌██. ██ ██▄▪▐█
//! ▀▀  █▪▀▀▀ ▀█▄▀▪ ▀█▄▀▪ ▀█▄▀▪▀▀▀▀▀• ·▀▀▀▀
//!
//! **MOOODB** is a relational database management system

mod io;
mod page;
mod storage;

// rkyv for network

/*
#[cfg(test)]
mod test {
    use tracing::level_filters::LevelFilter;
    use tracing_subscriber::{Layer, layer::SubscriberExt, util::SubscriberInitExt};

    use crate::{buffer::storage::Storage, mem_io::MemIO};

    #[test]
    fn asd() {
        let stdout_layer = tracing_subscriber::fmt::layer();
        tracing_subscriber::registry()
            .with(stdout_layer.with_filter(LevelFilter::TRACE))
            .init();

        let rt = tokio::runtime::Runtime::new().unwrap();
        rt.block_on(async {
            let storage = Storage::new(Box::new(MemIO::new()), 18).await;

            for _ in 0..10 {
                tracing::debug!("got page {}", storage.get_free_page().await.0);
            }

            storage.free_page(2).await;
            storage.free_page(4).await;
            storage.free_page(7).await;

            for _ in 0..12 {
                tracing::debug!("got page {}", storage.get_free_page().await.0);
            }
        });
    }
}
*/
