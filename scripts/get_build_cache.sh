#!/usr/bin/env bash
# Fetch the precompiled project build of main (published by CI to the `lake-cache`
# release) into .lake/build, so that only changed modules have to be compiled.
# Run after `lake exe cache get`.
set -euo pipefail
base="https://github.com/Rogerhu12/continuous-flexibility/releases/download/lake-cache"
tmp="$(mktemp -d)"
curl -fL "$base/lake-build.tar.zst" -o "$tmp/lake-build.tar.zst"
curl -fL "$base/lake-build.commit" -o "$tmp/lake-build.commit" || true
tar --zstd -xf "$tmp/lake-build.tar.zst"
echo "restored .lake/build from main at $(cat "$tmp/lake-build.commit" 2>/dev/null || echo unknown)"
