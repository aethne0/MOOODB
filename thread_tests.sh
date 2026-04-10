#!/usr/bin/env bash
set -euo pipefail

run_shuttle() {
    echo "==> shuttle"
    RUSTFLAGS="--cfg shuttle" cargo test --features shuttle "$@"
}

run_loom() {
    echo "==> loom"
    RUSTFLAGS="--cfg loom" cargo test --features loom "$@"
}

case "${1:-all}" in
    --shuttle) run_shuttle ;;
    --loom)    run_loom ;;
    all)       run_shuttle; run_loom ;;
    *) echo "usage: $0 [--shuttle | --loom]" >&2; exit 1 ;;
esac
