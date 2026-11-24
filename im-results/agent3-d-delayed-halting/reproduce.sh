#!/usr/bin/env bash
set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
root="$(cd "$here/../.." && pwd)"
tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT
base64 -d "$here/Proofs.tar.xz.b64" > "$tmp/Proofs.tar.xz"
echo "c8046d74afb2a254d486e9eeadcb29b9634e41009a3ebd561a5357d2d219d99d  $tmp/Proofs.tar.xz" | sha256sum -c -
tar -xJf "$tmp/Proofs.tar.xz" -C "$tmp"
base64 -d "$root/im-results/agent31-cryptid-boundary/Boundary.lean.xz.b64" | xz -d > "$tmp/Boundary.lean"
cp "$root/im-results/agent32-cryptid-third/"{CryptidSix,CryptidTriplePairs}.lean "$tmp/"
cd "$tmp"
export LEAN_PATH=.
for f in Boundary CryptidSix CryptidTriplePairs DelayedHalting; do lean -o "$f.olean" "$f.lean"; done
lean DelaySource.lean
