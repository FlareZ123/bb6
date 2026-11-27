#!/usr/bin/env bash
set -euo pipefail
base="$PWD/im-results/agent48-raw139-e0-1la"
work="$PWD/.tmp/a48-oneLA-check"
graft="$1"
test "$(cat "$work/source-sha")" = 1a513302a4333d3aff095a9350281b35c3b9f209
test "$(cat "$graft/source-sha")" = 97d34779a50855ff40b480fff458aed96056d8f3
(cd "$graft"; sha256sum -c <<'EOF'
e6debaf6d01e5b06bce2404a750899954fec2072f82b2b41634ac61c35ae540f  partition.json
0b1d01399e25c52e7413f6bd11e5e9dd7ce899c2e740f14efc9f8520ed54d0ef  spec-compact.json
EOF
)
gzip -dc "$base/repair-width4.py.gz" > /tmp/repair-width4.py
echo 'd615837aa9054086870f9e8e8bf517b8561702ddea094437af9d86f5b49ef015  /tmp/repair-width4.py' | sha256sum -c
python3 /tmp/repair-width4.py "$work/imports" "$work/extern" "$graft/partition.json" "$graft/spec-compact.json"
git rev-parse HEAD > "$work/source-sha"
