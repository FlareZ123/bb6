#!/usr/bin/env bash
set -euo pipefail
base="$PWD/im-results/agent3-raw139-e0-oneLB"
checker="$PWD/im-results/agent48-raw139-e0-0re"
export PYTHONPATH="$PWD/im-results/agent48-raw139-f1-oneRA:$PWD/im-results/agent48-raw139-f1-oneLA:$checker"
work="$PWD/.tmp/a3-oneLB-discovery"
mkdir -p "$work"
g++ -std=c++17 -O3 "$checker/replay.cpp" -o "$work/replay"
python3 "$checker/test_replay.py" "$work/replay"
python3 -u "$base/discover-rest.py" "$work/replay" "$work" "$@" | tee "$work/search.log"
