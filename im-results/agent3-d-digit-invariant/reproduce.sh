#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT
base64 -d DigitInvariant.lean.xz.b64 | xz -d > "$tmp/DigitInvariant.lean"
echo "964293fdaa19b2e5ce26556c3870d8c52d9a7703bcea9e6beeea0aa10cd9920f  $tmp/DigitInvariant.lean" | sha256sum -c
lean "$tmp/DigitInvariant.lean"
