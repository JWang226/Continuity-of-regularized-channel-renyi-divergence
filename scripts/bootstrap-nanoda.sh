#!/usr/bin/env bash
# Copyright (c) 2026 Jinzhao Wang. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
# Authors: Jinzhao Wang (AI-assisted formalization)

# Rebuild the independent checker from its exact, unmodified upstream revision.
# Uses existing Cargo, or installs Rust 1.98.1 only inside this directory.
set -euo pipefail
verification_root=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
tools_dir="$verification_root/.lake/nanoda-tools"
nanoda_dir="$tools_dir/nanoda_lib"
nanoda_commit=3a2407216ee84a75f9e1aead6803d0578be06ae7
rust_version=1.98.1
rustup_version=1.29.1
installer_sha256=7d0ea0f8eba7fa1ebfe998091cd7ec4501e33ec5ca6b884eb4d894d7da5170af
mkdir -p "$tools_dir"
if [ -d /Library/Developer/CommandLineTools ]; then
  export DEVELOPER_DIR=/Library/Developer/CommandLineTools
fi

sha256_file() {
  if command -v sha256sum >/dev/null 2>&1; then
    sha256sum "$1" | awk '{print $1}'
  else
    shasum -a 256 "$1" | awk '{print $1}'
  fi
}

if command -v cargo >/dev/null 2>&1; then
  cargo_binary=$(command -v cargo)
  rustc_binary=$(command -v rustc)
  printf 'Using existing Cargo: %s\n' "$cargo_binary"
else
  export RUSTUP_HOME="$tools_dir/rustup"
  export CARGO_HOME="$tools_dir/cargo"
  export PATH="$CARGO_HOME/bin:$PATH"
  cargo_binary="$CARGO_HOME/bin/cargo"
  rustc_binary="$CARGO_HOME/bin/rustc"
  if [ ! -x "$cargo_binary" ]; then
    installer="$tools_dir/rustup-init-$rustup_version.sh"
    curl -fsSL --proto '=https' --tlsv1.2 \
      "https://raw.githubusercontent.com/rust-lang/rustup/$rustup_version/rustup-init.sh" \
      -o "$installer"
    actual_installer_sha256=$(sha256_file "$installer")
    if [ "$actual_installer_sha256" != "$installer_sha256" ]; then
      printf 'Rust installer checksum mismatch; refusing execution.\n' >&2
      exit 1
    fi
    RUSTUP_VERSION="$rustup_version" sh "$installer" -y --no-modify-path \
      --profile minimal --default-toolchain "$rust_version"
  fi
  # Keep the already-validated local compiler if its default is the exact version.
  if ! "$rustc_binary" --version | awk -v expected="$rust_version" '$2 == expected { ok=1 } END { exit !ok }'; then
    "$CARGO_HOME/bin/rustup" toolchain install "$rust_version" --profile minimal
    export RUSTUP_TOOLCHAIN="$rust_version"
  fi
fi

if [ ! -e "$nanoda_dir" ]; then
  git clone --no-checkout https://github.com/ammkrn/nanoda_lib.git "$nanoda_dir"
  git -C "$nanoda_dir" checkout --detach "$nanoda_commit"
else
  actual_commit=$(git -C "$nanoda_dir" rev-parse HEAD)
  if [ "$actual_commit" != "$nanoda_commit" ]; then
    printf 'Existing Nanoda checkout is at another revision; refusing to change it.\n' >&2
    exit 1
  fi
fi
if [ -n "$(git -C "$nanoda_dir" status --porcelain --untracked-files=no)" ]; then
  printf 'Nanoda tracked source files have changes; refusing an unpinned build.\n' >&2
  exit 1
fi

printf 'Nanoda source revision: %s\n' "$nanoda_commit"
"$rustc_binary" --version --verbose
"$cargo_binary" --version
(
  cd "$nanoda_dir"
  "$cargo_binary" build --locked --release
  "$cargo_binary" test --locked --release
)
printf 'Binary SHA256: %s\n' "$(sha256_file "$nanoda_dir/target/release/nanoda_bin")"
printf 'Independent checker ready: %s\n' "$nanoda_dir/target/release/nanoda_bin"
